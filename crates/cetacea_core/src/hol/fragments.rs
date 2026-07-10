//! Statement classification, transitive proof receipts, and teaching policy.
//!
//! This module deliberately consumes resolved, checked core objects. Surface
//! annotations may request a profile, but they never get to assert a receipt.

use std::collections::BTreeSet;
use std::fmt;

use super::proofs::HolProofAudit;
use super::terms::{
    infer_type, normalize, ConstantId, CoreTerm, TermContext, TermError, TermSignature,
};
use super::types::{CoreType, FirstOrderStatus, TypeConstructorId, TypeError, TypeSignature};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum StatementFragment {
    Prop,
    FirstOrder,
    FirstOrderInductive,
    HigherOrder,
}

impl StatementFragment {
    fn combine(self, other: Self) -> Self {
        self.max(other)
    }
}

impl fmt::Display for StatementFragment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Prop => f.write_str("prop"),
            Self::FirstOrder => f.write_str("fol"),
            Self::FirstOrderInductive => f.write_str("fol+induction"),
            Self::HigherOrder => f.write_str("hol"),
        }
    }
}

/// Declaration facts needed only for fragment classification.
///
/// Keeping these facts out of `TypeSignature` and `TermSignature` means the
/// proof kernel does not need to know about course labels. The inductive
/// elaborator will populate this metadata from checked declarations.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FragmentMetadata {
    inductive_types: BTreeSet<TypeConstructorId>,
    structurally_recursive_constants: BTreeSet<ConstantId>,
}

impl FragmentMetadata {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn mark_inductive_type(&mut self, id: TypeConstructorId) {
        self.inductive_types.insert(id);
    }

    pub fn mark_structurally_recursive_constant(&mut self, id: ConstantId) {
        self.structurally_recursive_constants.insert(id);
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FragmentError {
    pub message: String,
}

impl FragmentError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for FragmentError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for FragmentError {}

impl From<TermError> for FragmentError {
    fn from(error: TermError) -> Self {
        Self::new(error.message)
    }
}

impl From<TypeError> for FragmentError {
    fn from(error: TypeError) -> Self {
        Self::new(error.message)
    }
}

/// Compute the least teaching fragment of a checked proposition.
///
/// The term is beta-normalized before inspection. This is important: a lambda
/// introduced as elaborator scaffolding and immediately eliminated must not
/// make an otherwise first-order statement look higher-order.
pub fn classify_statement(
    types: &TypeSignature,
    constants: &TermSignature,
    context: &TermContext,
    metadata: &FragmentMetadata,
    statement: &CoreTerm,
) -> Result<StatementFragment, FragmentError> {
    let actual_type = infer_type(types, constants, context, statement)?;
    if actual_type != CoreType::Prop {
        return Err(FragmentError::new(format!(
            "statement must have type `Prop`, but has type `{actual_type:?}`"
        )));
    }
    let normalized = normalize(types, constants, context, statement)?;
    classify_proposition(types, constants, context, metadata, &normalized)
}

fn classify_proposition(
    types: &TypeSignature,
    constants: &TermSignature,
    context: &TermContext,
    metadata: &FragmentMetadata,
    proposition: &CoreTerm,
) -> Result<StatementFragment, FragmentError> {
    match proposition {
        CoreTerm::Truth | CoreTerm::Falsity | CoreTerm::Bound(_) => Ok(StatementFragment::Prop),
        CoreTerm::Constant(id) => classify_nullary_proposition(types, metadata, *id, &[]),
        CoreTerm::TypeApplication {
            constant,
            arguments,
        } => classify_nullary_proposition(types, metadata, *constant, arguments),
        CoreTerm::And(left, right) | CoreTerm::Or(left, right) | CoreTerm::Implies(left, right) => {
            Ok(
                classify_proposition(types, constants, context, metadata, left)?.combine(
                    classify_proposition(types, constants, context, metadata, right)?,
                ),
            )
        }
        CoreTerm::Equality { ty, left, right } => {
            let type_fragment = classify_data_type(types, metadata, ty)?;
            if type_fragment == StatementFragment::HigherOrder {
                return Ok(StatementFragment::HigherOrder);
            }
            Ok(StatementFragment::FirstOrder
                .combine(type_fragment)
                .combine(classify_first_order_term(
                    types, constants, context, metadata, left,
                )?)
                .combine(classify_first_order_term(
                    types, constants, context, metadata, right,
                )?))
        }
        CoreTerm::Forall { domain, body } | CoreTerm::Exists { domain, body } => {
            let domain_fragment = classify_data_type(types, metadata, domain)?;
            let body_context = context.clone().with_bound(domain.clone());
            let body_fragment =
                classify_proposition(types, constants, &body_context, metadata, body)?;
            Ok(StatementFragment::FirstOrder
                .combine(domain_fragment)
                .combine(body_fragment))
        }
        CoreTerm::Membership {
            element_type,
            element,
            set,
        } => Ok(StatementFragment::FirstOrder
            .combine(classify_data_type(types, metadata, element_type)?)
            .combine(classify_first_order_term(
                types, constants, context, metadata, element,
            )?)
            .combine(classify_first_order_term(
                types, constants, context, metadata, set,
            )?)),
        CoreTerm::Subset {
            element_type,
            left,
            right,
        } => Ok(StatementFragment::FirstOrder
            .combine(classify_data_type(types, metadata, element_type)?)
            .combine(classify_first_order_term(
                types, constants, context, metadata, left,
            )?)
            .combine(classify_first_order_term(
                types, constants, context, metadata, right,
            )?)),
        CoreTerm::Apply { .. } => classify_declared_application(
            types,
            constants,
            context,
            metadata,
            proposition,
            ApplicationResult::Proposition,
        ),
        CoreTerm::Lambda { .. }
        | CoreTerm::Pair(_, _)
        | CoreTerm::First(_)
        | CoreTerm::Second(_)
        | CoreTerm::EmptySet { .. }
        | CoreTerm::UniverseSet { .. }
        | CoreTerm::SingletonSet(_)
        | CoreTerm::SetUnion(_, _)
        | CoreTerm::SetIntersection(_, _)
        | CoreTerm::SetDifference(_, _)
        | CoreTerm::SetComplement(_)
        | CoreTerm::SetProduct(_, _)
        | CoreTerm::Powerset { .. }
        | CoreTerm::SetBuilder { .. } => Ok(StatementFragment::HigherOrder),
    }
}

fn classify_first_order_term(
    types: &TypeSignature,
    constants: &TermSignature,
    context: &TermContext,
    metadata: &FragmentMetadata,
    term: &CoreTerm,
) -> Result<StatementFragment, FragmentError> {
    let ty = infer_type(types, constants, context, term)?;
    let type_fragment = classify_data_type(types, metadata, &ty)?;
    if type_fragment == StatementFragment::HigherOrder {
        return Ok(StatementFragment::HigherOrder);
    }

    match term {
        CoreTerm::Bound(_) => Ok(StatementFragment::FirstOrder.combine(type_fragment)),
        CoreTerm::Constant(id) => {
            let declaration_fragment = if metadata.structurally_recursive_constants.contains(id) {
                StatementFragment::FirstOrderInductive
            } else {
                StatementFragment::FirstOrder
            };
            Ok(declaration_fragment.combine(type_fragment))
        }
        CoreTerm::TypeApplication {
            constant,
            arguments,
        } => Ok(classify_type_arguments(types, metadata, arguments)?
            .combine(
                if metadata.structurally_recursive_constants.contains(constant) {
                    StatementFragment::FirstOrderInductive
                } else {
                    StatementFragment::FirstOrder
                },
            )
            .combine(type_fragment)),
        CoreTerm::Apply { .. } => classify_declared_application(
            types,
            constants,
            context,
            metadata,
            term,
            ApplicationResult::Data,
        ),
        CoreTerm::Pair(left, right) => Ok(type_fragment
            .combine(classify_first_order_term(
                types, constants, context, metadata, left,
            )?)
            .combine(classify_first_order_term(
                types, constants, context, metadata, right,
            )?)),
        CoreTerm::First(pair) | CoreTerm::Second(pair) => Ok(type_fragment.combine(
            classify_first_order_term(types, constants, context, metadata, pair)?,
        )),
        CoreTerm::EmptySet { element_type } | CoreTerm::UniverseSet { element_type } => {
            Ok(type_fragment.combine(classify_data_type(types, metadata, element_type)?))
        }
        CoreTerm::SingletonSet(element) | CoreTerm::SetComplement(element) => Ok(type_fragment
            .combine(classify_first_order_term(
                types, constants, context, metadata, element,
            )?)),
        CoreTerm::SetUnion(left, right)
        | CoreTerm::SetIntersection(left, right)
        | CoreTerm::SetDifference(left, right)
        | CoreTerm::SetProduct(left, right) => Ok(type_fragment
            .combine(classify_first_order_term(
                types, constants, context, metadata, left,
            )?)
            .combine(classify_first_order_term(
                types, constants, context, metadata, right,
            )?)),
        CoreTerm::Powerset { element_type, set } => Ok(type_fragment
            .combine(classify_data_type(types, metadata, element_type)?)
            .combine(classify_first_order_term(
                types, constants, context, metadata, set,
            )?)),
        CoreTerm::SetBuilder { element_type, body } => {
            let body_context = context.clone().with_bound(element_type.clone());
            Ok(type_fragment
                .combine(classify_data_type(types, metadata, element_type)?)
                .combine(classify_proposition(
                    types,
                    constants,
                    &body_context,
                    metadata,
                    body,
                )?))
        }
        CoreTerm::Lambda { .. }
        | CoreTerm::Truth
        | CoreTerm::Falsity
        | CoreTerm::And(_, _)
        | CoreTerm::Or(_, _)
        | CoreTerm::Implies(_, _)
        | CoreTerm::Equality { .. }
        | CoreTerm::Forall { .. }
        | CoreTerm::Exists { .. }
        | CoreTerm::Membership { .. }
        | CoreTerm::Subset { .. } => Ok(StatementFragment::HigherOrder),
    }
}

#[derive(Clone, Copy)]
enum ApplicationResult {
    Proposition,
    Data,
}

fn classify_declared_application(
    types: &TypeSignature,
    constants: &TermSignature,
    context: &TermContext,
    metadata: &FragmentMetadata,
    application: &CoreTerm,
    expected_result: ApplicationResult,
) -> Result<StatementFragment, FragmentError> {
    let mut arguments = Vec::new();
    let head = application_spine(application, &mut arguments);
    let (mut current_type, mut fragment) = if let Some((id, type_arguments)) = declared_head(head) {
        let fragment = classify_type_arguments(types, metadata, type_arguments)?.combine(
            if metadata.structurally_recursive_constants.contains(&id) {
                StatementFragment::FirstOrderInductive
            } else {
                StatementFragment::FirstOrder
            },
        );
        (infer_type(types, constants, context, head)?, fragment)
    } else if matches!(head, CoreTerm::Bound(_)) {
        // Rank-one theorem symbol parameters behave like declared symbols when
        // saturated. An enclosing object-level quantifier over an arrow type
        // still raises the enclosing formula to HOL, and partial application
        // is detected by the result-type check below.
        (
            infer_type(types, constants, context, head)?,
            StatementFragment::FirstOrder,
        )
    } else {
        // Retained lambdas and other computed function values are higher-order.
        return Ok(StatementFragment::HigherOrder);
    };

    for argument in arguments {
        let CoreType::Arrow(domain, codomain) = current_type else {
            return Err(FragmentError::new(
                "well-typed application has more arguments than its declared symbol type",
            ));
        };
        let domain_fragment = classify_data_type(types, metadata, &domain)?;
        if domain_fragment == StatementFragment::HigherOrder {
            return Ok(StatementFragment::HigherOrder);
        }
        fragment = fragment
            .combine(domain_fragment)
            .combine(classify_first_order_term(
                types, constants, context, metadata, argument,
            )?);
        current_type = *codomain;
    }

    match expected_result {
        ApplicationResult::Proposition => {
            if current_type == CoreType::Prop {
                Ok(fragment)
            } else if matches!(current_type, CoreType::Arrow(_, _)) {
                Ok(StatementFragment::HigherOrder)
            } else {
                Err(FragmentError::new(format!(
                    "atomic proposition application has result type `{current_type:?}`"
                )))
            }
        }
        ApplicationResult::Data => {
            let result_fragment = classify_data_type(types, metadata, &current_type)?;
            if result_fragment == StatementFragment::HigherOrder {
                Ok(StatementFragment::HigherOrder)
            } else {
                Ok(fragment.combine(result_fragment))
            }
        }
    }
}

fn declared_head(term: &CoreTerm) -> Option<(ConstantId, &[CoreType])> {
    match term {
        CoreTerm::Constant(id) => Some((*id, &[])),
        CoreTerm::TypeApplication {
            constant,
            arguments,
        } => Some((*constant, arguments)),
        _ => None,
    }
}

fn classify_nullary_proposition(
    types: &TypeSignature,
    metadata: &FragmentMetadata,
    id: ConstantId,
    type_arguments: &[CoreType],
) -> Result<StatementFragment, FragmentError> {
    let declaration_fragment = if metadata.structurally_recursive_constants.contains(&id) {
        StatementFragment::FirstOrderInductive
    } else if type_arguments.is_empty() {
        StatementFragment::Prop
    } else {
        StatementFragment::FirstOrder
    };
    Ok(declaration_fragment.combine(classify_type_arguments(types, metadata, type_arguments)?))
}

fn classify_type_arguments(
    types: &TypeSignature,
    metadata: &FragmentMetadata,
    arguments: &[CoreType],
) -> Result<StatementFragment, FragmentError> {
    arguments.iter().try_fold(
        if arguments.is_empty() {
            StatementFragment::Prop
        } else {
            StatementFragment::FirstOrder
        },
        |fragment, argument| Ok(fragment.combine(classify_data_type(types, metadata, argument)?)),
    )
}

fn application_spine<'a>(term: &'a CoreTerm, arguments: &mut Vec<&'a CoreTerm>) -> &'a CoreTerm {
    match term {
        CoreTerm::Apply { function, argument } => {
            let head = application_spine(function, arguments);
            arguments.push(argument);
            head
        }
        _ => term,
    }
}

fn classify_data_type(
    types: &TypeSignature,
    metadata: &FragmentMetadata,
    ty: &CoreType,
) -> Result<StatementFragment, FragmentError> {
    if types.first_order_status(ty)? == FirstOrderStatus::HigherOrder {
        return Ok(StatementFragment::HigherOrder);
    }
    if type_mentions_inductive(ty, metadata) {
        Ok(StatementFragment::FirstOrderInductive)
    } else {
        Ok(StatementFragment::FirstOrder)
    }
}

fn type_mentions_inductive(ty: &CoreType, metadata: &FragmentMetadata) -> bool {
    match ty {
        CoreType::Prop | CoreType::Parameter(_) => false,
        CoreType::Constructor { id, arguments } => {
            metadata.inductive_types.contains(id)
                || arguments
                    .iter()
                    .any(|argument| type_mentions_inductive(argument, metadata))
        }
        CoreType::Arrow(domain, codomain) | CoreType::Product(domain, codomain) => {
            type_mentions_inductive(domain, metadata) || type_mentions_inductive(codomain, metadata)
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ProofFeature {
    Classical,
    Induction,
    StructuralRecursion,
    HigherOrderAbstraction,
    HigherOrderInstantiation,
    FunctionExtensionality,
    PropositionalExtensionality,
    Choice,
}

impl ProofFeature {
    pub fn minimum_fragment(self) -> StatementFragment {
        match self {
            Self::Classical => StatementFragment::Prop,
            Self::Induction | Self::StructuralRecursion => StatementFragment::FirstOrderInductive,
            Self::HigherOrderAbstraction
            | Self::HigherOrderInstantiation
            | Self::FunctionExtensionality
            | Self::PropositionalExtensionality
            | Self::Choice => StatementFragment::HigherOrder,
        }
    }
}

pub fn proof_features_from_audit(audit: HolProofAudit) -> BTreeSet<ProofFeature> {
    let mut features = BTreeSet::new();
    if audit.uses_induction() {
        features.insert(ProofFeature::Induction);
    }
    if audit.uses_classical() {
        features.insert(ProofFeature::Classical);
    }
    features
}

impl fmt::Display for ProofFeature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Classical => f.write_str("classical"),
            Self::Induction => f.write_str("induction"),
            Self::StructuralRecursion => f.write_str("structural-recursion"),
            Self::HigherOrderAbstraction => f.write_str("higher-order-abstraction"),
            Self::HigherOrderInstantiation => f.write_str("higher-order-instantiation"),
            Self::FunctionExtensionality => f.write_str("function-extensionality"),
            Self::PropositionalExtensionality => f.write_str("propositional-extensionality"),
            Self::Choice => f.write_str("choice"),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DeclarationId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum EvidenceStatus {
    Checked,
    Incomplete,
    TrustedAxiom,
}

/// Auditable closure of a declaration's checked evidence and dependencies.
///
/// Fields are private so callers cannot claim a smaller transitive closure.
/// Receipts are constructed only by folding already-computed dependency
/// receipts in declaration order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofReceipt {
    statement_fragment: StatementFragment,
    dependency_fragment: StatementFragment,
    direct_features: BTreeSet<ProofFeature>,
    transitive_features: BTreeSet<ProofFeature>,
    direct_dependencies: BTreeSet<DeclarationId>,
    transitive_dependencies: BTreeSet<DeclarationId>,
    axiom_dependencies: BTreeSet<DeclarationId>,
    incomplete_dependencies: BTreeSet<DeclarationId>,
}

impl ProofReceipt {
    fn derive<'a>(
        statement_fragment: StatementFragment,
        direct_features: impl IntoIterator<Item = ProofFeature>,
        dependencies: impl IntoIterator<Item = &'a DeclarationReceipt>,
    ) -> Self {
        let direct_features = direct_features.into_iter().collect::<BTreeSet<_>>();
        let mut receipt = Self {
            statement_fragment,
            dependency_fragment: StatementFragment::Prop,
            transitive_features: direct_features.clone(),
            direct_features,
            direct_dependencies: BTreeSet::new(),
            transitive_dependencies: BTreeSet::new(),
            axiom_dependencies: BTreeSet::new(),
            incomplete_dependencies: BTreeSet::new(),
        };

        for dependency in dependencies {
            receipt.direct_dependencies.insert(dependency.id);
            receipt.transitive_dependencies.insert(dependency.id);
            receipt
                .transitive_dependencies
                .extend(dependency.receipt.transitive_dependencies.iter().copied());
            receipt
                .transitive_features
                .extend(dependency.receipt.transitive_features.iter().copied());
            receipt
                .axiom_dependencies
                .extend(dependency.receipt.axiom_dependencies.iter().copied());
            receipt
                .incomplete_dependencies
                .extend(dependency.receipt.incomplete_dependencies.iter().copied());
            receipt.dependency_fragment = receipt
                .dependency_fragment
                .combine(dependency.receipt.required_fragment());

            match dependency.status {
                EvidenceStatus::Checked => {}
                EvidenceStatus::Incomplete => {
                    receipt.incomplete_dependencies.insert(dependency.id);
                }
                EvidenceStatus::TrustedAxiom => {
                    receipt.axiom_dependencies.insert(dependency.id);
                }
            }
        }

        receipt
    }

    pub fn statement_fragment(&self) -> StatementFragment {
        self.statement_fragment
    }

    pub fn dependency_fragment(&self) -> StatementFragment {
        self.dependency_fragment
    }

    pub fn required_fragment(&self) -> StatementFragment {
        self.transitive_features.iter().fold(
            self.statement_fragment.combine(self.dependency_fragment),
            |fragment, feature| fragment.combine(feature.minimum_fragment()),
        )
    }

    pub fn direct_features(&self) -> &BTreeSet<ProofFeature> {
        &self.direct_features
    }

    pub fn transitive_features(&self) -> &BTreeSet<ProofFeature> {
        &self.transitive_features
    }

    pub fn direct_dependencies(&self) -> &BTreeSet<DeclarationId> {
        &self.direct_dependencies
    }

    pub fn transitive_dependencies(&self) -> &BTreeSet<DeclarationId> {
        &self.transitive_dependencies
    }

    pub fn axiom_dependencies(&self) -> &BTreeSet<DeclarationId> {
        &self.axiom_dependencies
    }

    pub fn incomplete_dependencies(&self) -> &BTreeSet<DeclarationId> {
        &self.incomplete_dependencies
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclarationReceipt {
    id: DeclarationId,
    status: EvidenceStatus,
    receipt: ProofReceipt,
}

impl DeclarationReceipt {
    pub(super) fn checked<'a>(
        id: DeclarationId,
        statement_fragment: StatementFragment,
        direct_features: impl IntoIterator<Item = ProofFeature>,
        dependencies: impl IntoIterator<Item = &'a Self>,
    ) -> Self {
        Self {
            id,
            status: EvidenceStatus::Checked,
            receipt: ProofReceipt::derive(statement_fragment, direct_features, dependencies),
        }
    }

    pub(super) fn incomplete_with_dependencies<'a>(
        id: DeclarationId,
        statement_fragment: StatementFragment,
        direct_features: impl IntoIterator<Item = ProofFeature>,
        dependencies: impl IntoIterator<Item = &'a Self>,
    ) -> Self {
        Self {
            id,
            status: EvidenceStatus::Incomplete,
            receipt: ProofReceipt::derive(statement_fragment, direct_features, dependencies),
        }
    }

    #[cfg(test)]
    fn incomplete<'a>(
        id: DeclarationId,
        statement_fragment: StatementFragment,
        direct_features: impl IntoIterator<Item = ProofFeature>,
        dependencies: impl IntoIterator<Item = &'a Self>,
    ) -> Self {
        Self::incomplete_with_dependencies(id, statement_fragment, direct_features, dependencies)
    }

    pub(super) fn trusted_axiom_with_dependencies<'a>(
        id: DeclarationId,
        statement_fragment: StatementFragment,
        dependencies: impl IntoIterator<Item = &'a Self>,
    ) -> Self {
        Self {
            id,
            status: EvidenceStatus::TrustedAxiom,
            receipt: ProofReceipt::derive(statement_fragment, [], dependencies),
        }
    }

    #[cfg(test)]
    fn trusted_axiom(id: DeclarationId, statement_fragment: StatementFragment) -> Self {
        Self::trusted_axiom_with_dependencies(id, statement_fragment, [])
    }

    pub fn id(&self) -> DeclarationId {
        self.id
    }

    pub fn status(&self) -> EvidenceStatus {
        self.status
    }

    pub fn proof(&self) -> &ProofReceipt {
        &self.receipt
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum TeachingProfile {
    Prop,
    FirstOrder,
    FirstOrderInductive,
    HigherOrder,
}

impl TeachingProfile {
    pub fn maximum_fragment(self) -> StatementFragment {
        match self {
            Self::Prop => StatementFragment::Prop,
            Self::FirstOrder => StatementFragment::FirstOrder,
            Self::FirstOrderInductive => StatementFragment::FirstOrderInductive,
            Self::HigherOrder => StatementFragment::HigherOrder,
        }
    }

    fn base_features(self) -> BTreeSet<ProofFeature> {
        match self {
            Self::Prop | Self::FirstOrder => BTreeSet::new(),
            Self::FirstOrderInductive => {
                [ProofFeature::Induction, ProofFeature::StructuralRecursion]
                    .into_iter()
                    .collect()
            }
            Self::HigherOrder => [
                ProofFeature::Induction,
                ProofFeature::StructuralRecursion,
                ProofFeature::HigherOrderAbstraction,
                ProofFeature::HigherOrderInstantiation,
            ]
            .into_iter()
            .collect(),
        }
    }
}

/// Policy defaults are constructive and trust-free for every profile,
/// including HOL. Strong principles require separate, explicit permission.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiptPolicy {
    profile: TeachingProfile,
    allowed_features: BTreeSet<ProofFeature>,
    allowed_axioms: BTreeSet<DeclarationId>,
    allow_any_axiom: bool,
    allow_incomplete: bool,
    allowed_dependencies: Option<BTreeSet<DeclarationId>>,
}

impl ReceiptPolicy {
    pub fn new(profile: TeachingProfile) -> Self {
        Self {
            profile,
            allowed_features: profile.base_features(),
            allowed_axioms: BTreeSet::new(),
            allow_any_axiom: false,
            allow_incomplete: false,
            allowed_dependencies: None,
        }
    }

    pub fn allow_feature(&mut self, feature: ProofFeature) {
        self.allowed_features.insert(feature);
    }

    pub fn allow_classical(&mut self) {
        self.allow_feature(ProofFeature::Classical);
    }

    pub fn allow_extensionality(&mut self) {
        self.allow_feature(ProofFeature::FunctionExtensionality);
        self.allow_feature(ProofFeature::PropositionalExtensionality);
    }

    pub fn allow_choice(&mut self) {
        self.allow_feature(ProofFeature::Choice);
    }

    pub fn allow_axiom(&mut self, id: DeclarationId) {
        self.allowed_axioms.insert(id);
    }

    pub fn allow_any_axiom(&mut self) {
        self.allow_any_axiom = true;
    }

    pub fn allow_incomplete(&mut self) {
        self.allow_incomplete = true;
    }

    pub fn restrict_dependencies(&mut self, allowed: impl IntoIterator<Item = DeclarationId>) {
        self.allowed_dependencies = Some(allowed.into_iter().collect());
    }

    pub fn check(&self, declaration: &DeclarationReceipt) -> Vec<PolicyViolation> {
        let mut violations = Vec::new();
        let receipt = declaration.proof();
        let maximum = self.profile.maximum_fragment();

        if receipt.statement_fragment > maximum {
            violations.push(PolicyViolation::StatementFragmentExceeds {
                actual: receipt.statement_fragment,
                maximum,
            });
        }
        if receipt.dependency_fragment > maximum {
            violations.push(PolicyViolation::DependencyFragmentExceeds {
                actual: receipt.dependency_fragment,
                maximum,
            });
        }

        for feature in &receipt.transitive_features {
            if !self.allowed_features.contains(feature) {
                violations.push(PolicyViolation::FeatureNotAllowed(*feature));
            } else if feature.minimum_fragment() > maximum {
                violations.push(PolicyViolation::FeatureFragmentExceeds {
                    feature: *feature,
                    maximum,
                });
            }
        }

        if declaration.status == EvidenceStatus::TrustedAxiom
            && !self.axiom_is_allowed(declaration.id)
        {
            violations.push(PolicyViolation::TrustedAxiomNotAllowed(declaration.id));
        }
        for dependency in &receipt.axiom_dependencies {
            if !self.axiom_is_allowed(*dependency) {
                violations.push(PolicyViolation::TrustedAxiomNotAllowed(*dependency));
            }
        }

        if !self.allow_incomplete {
            if declaration.status == EvidenceStatus::Incomplete {
                violations.push(PolicyViolation::IncompleteNotAllowed(declaration.id));
            }
            violations.extend(
                receipt
                    .incomplete_dependencies
                    .iter()
                    .copied()
                    .map(PolicyViolation::IncompleteNotAllowed),
            );
        }

        if let Some(allowed) = &self.allowed_dependencies {
            violations.extend(
                receipt
                    .transitive_dependencies
                    .difference(allowed)
                    .copied()
                    .map(PolicyViolation::DependencyNotAllowed),
            );
        }

        violations.sort();
        violations.dedup();
        violations
    }

    fn axiom_is_allowed(&self, id: DeclarationId) -> bool {
        self.allow_any_axiom || self.allowed_axioms.contains(&id)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum PolicyViolation {
    StatementFragmentExceeds {
        actual: StatementFragment,
        maximum: StatementFragment,
    },
    DependencyFragmentExceeds {
        actual: StatementFragment,
        maximum: StatementFragment,
    },
    FeatureNotAllowed(ProofFeature),
    FeatureFragmentExceeds {
        feature: ProofFeature,
        maximum: StatementFragment,
    },
    TrustedAxiomNotAllowed(DeclarationId),
    IncompleteNotAllowed(DeclarationId),
    DependencyNotAllowed(DeclarationId),
}

impl fmt::Display for PolicyViolation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::StatementFragmentExceeds { actual, maximum } => write!(
                f,
                "statement fragment `{actual}` exceeds profile maximum `{maximum}`"
            ),
            Self::DependencyFragmentExceeds { actual, maximum } => write!(
                f,
                "dependency fragment `{actual}` exceeds profile maximum `{maximum}`"
            ),
            Self::FeatureNotAllowed(feature) => {
                write!(f, "proof feature `{feature}` is not allowed")
            }
            Self::FeatureFragmentExceeds { feature, maximum } => write!(
                f,
                "proof feature `{feature}` exceeds profile maximum `{maximum}`"
            ),
            Self::TrustedAxiomNotAllowed(id) => {
                write!(f, "trusted axiom `{}` is not allowed", id.0)
            }
            Self::IncompleteNotAllowed(id) => {
                write!(f, "incomplete declaration `{}` is not allowed", id.0)
            }
            Self::DependencyNotAllowed(id) => {
                write!(f, "declaration dependency `{}` is not allowed", id.0)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::types::TypeParameter;

    struct Fixture {
        types: TypeSignature,
        constants: TermSignature,
        metadata: FragmentMetadata,
        nat: CoreType,
        list_nat: CoreType,
        a: ConstantId,
        predicate: ConstantId,
        relation: ConstantId,
        recursive_predicate: ConstantId,
    }

    fn fixture() -> Fixture {
        let mut types = TypeSignature::new();
        let nat_id = types.declare("Nat", 0, true).expect("Nat");
        let list_id = types.declare("List", 1, true).expect("List");
        types.declare_legacy_set("Set").expect("legacy Set");
        let nat = CoreType::constructor(nat_id, Vec::new());
        let list_nat = CoreType::constructor(list_id, vec![nat.clone()]);

        let mut constants = TermSignature::new();
        let a = constants
            .declare(&types, "a", nat.clone())
            .expect("individual");
        let predicate = constants
            .declare(&types, "P", CoreType::arrow(nat.clone(), CoreType::Prop))
            .expect("predicate");
        let relation = constants
            .declare(
                &types,
                "R",
                CoreType::arrow(nat.clone(), CoreType::arrow(nat.clone(), CoreType::Prop)),
            )
            .expect("relation");
        let recursive_predicate = constants
            .declare(&types, "Even", CoreType::arrow(nat.clone(), CoreType::Prop))
            .expect("recursive predicate");

        let mut metadata = FragmentMetadata::new();
        metadata.mark_inductive_type(list_id);
        metadata.mark_structurally_recursive_constant(recursive_predicate);

        Fixture {
            types,
            constants,
            metadata,
            nat,
            list_nat,
            a,
            predicate,
            relation,
            recursive_predicate,
        }
    }

    fn classify(fixture: &Fixture, context: &TermContext, term: &CoreTerm) -> StatementFragment {
        classify_statement(
            &fixture.types,
            &fixture.constants,
            context,
            &fixture.metadata,
            term,
        )
        .expect("classify statement")
    }

    #[test]
    fn propositional_atoms_and_connectives_stay_propositional() {
        let fixture = fixture();
        let context = TermContext::new().with_bound(CoreType::Prop);
        let statement = CoreTerm::implies(CoreTerm::Bound(0), CoreTerm::Bound(0));
        assert_eq!(
            classify(&fixture, &context, &statement),
            StatementFragment::Prop
        );
    }

    #[test]
    fn saturated_predicates_and_first_order_quantifiers_are_fol() {
        let fixture = fixture();
        let statement = CoreTerm::forall(
            fixture.nat.clone(),
            CoreTerm::apply(CoreTerm::Constant(fixture.predicate), CoreTerm::Bound(0)),
        );
        assert_eq!(
            classify(&fixture, &TermContext::new(), &statement),
            StatementFragment::FirstOrder
        );
    }

    #[test]
    fn product_terms_and_projections_preserve_the_least_fragment() {
        let fixture = fixture();
        let product = CoreType::product(fixture.nat.clone(), fixture.nat.clone());
        let projected = CoreTerm::first(CoreTerm::Bound(0));
        let statement = CoreTerm::forall(
            product,
            CoreTerm::equality(fixture.nat.clone(), projected.clone(), projected),
        );
        assert_eq!(
            classify(&fixture, &TermContext::new(), &statement),
            StatementFragment::FirstOrder
        );

        let proposition_product = CoreType::product(fixture.nat.clone(), CoreType::Prop);
        assert_eq!(
            classify(
                &fixture,
                &TermContext::new(),
                &CoreTerm::forall(proposition_product, CoreTerm::Truth),
            ),
            StatementFragment::HigherOrder
        );
    }

    #[test]
    fn legacy_set_membership_and_comprehension_remain_first_order() {
        let mut fixture = fixture();
        let set_nat = fixture
            .types
            .legacy_set_type(fixture.nat.clone())
            .expect("Set Nat");
        let set = fixture
            .constants
            .declare(&fixture.types, "A", set_nat.clone())
            .expect("set constant");
        let membership = CoreTerm::membership(
            fixture.nat.clone(),
            CoreTerm::Constant(fixture.a),
            CoreTerm::Constant(set),
        );
        assert_eq!(
            classify(&fixture, &TermContext::new(), &membership),
            StatementFragment::FirstOrder
        );

        let quantified = CoreTerm::forall(
            set_nat,
            CoreTerm::membership(
                fixture.nat.clone(),
                CoreTerm::Constant(fixture.a),
                CoreTerm::Bound(0),
            ),
        );
        assert_eq!(
            classify(&fixture, &TermContext::new(), &quantified),
            StatementFragment::FirstOrder
        );

        let builder = CoreTerm::set_builder(
            fixture.nat.clone(),
            CoreTerm::equality(
                fixture.nat.clone(),
                CoreTerm::Bound(0),
                CoreTerm::Constant(fixture.a),
            ),
        );
        let builder_membership =
            CoreTerm::membership(fixture.nat.clone(), CoreTerm::Constant(fixture.a), builder);
        assert_eq!(
            classify(&fixture, &TermContext::new(), &builder_membership),
            StatementFragment::FirstOrder
        );
    }

    #[test]
    fn saturated_first_order_function_and_relation_symbols_stay_fol() {
        let mut fixture = fixture();
        let function = fixture
            .constants
            .declare(
                &fixture.types,
                "f",
                CoreType::arrow(fixture.nat.clone(), fixture.nat.clone()),
            )
            .expect("function");
        let function_value =
            CoreTerm::apply(CoreTerm::Constant(function), CoreTerm::Constant(fixture.a));
        let statement = CoreTerm::apply(
            CoreTerm::apply(CoreTerm::Constant(fixture.relation), function_value),
            CoreTerm::Constant(fixture.a),
        );
        assert_eq!(
            classify(&fixture, &TermContext::new(), &statement),
            StatementFragment::FirstOrder
        );
    }

    #[test]
    fn beta_scaffolding_does_not_spuriously_taint_a_statement() {
        let fixture = fixture();
        let predicate_body =
            CoreTerm::apply(CoreTerm::Constant(fixture.predicate), CoreTerm::Bound(0));
        let statement = CoreTerm::apply(
            CoreTerm::lambda(fixture.nat.clone(), predicate_body),
            CoreTerm::Constant(fixture.a),
        );
        assert_eq!(
            classify(&fixture, &TermContext::new(), &statement),
            StatementFragment::FirstOrder
        );
    }

    #[test]
    fn higher_order_quantification_is_detected() {
        let fixture = fixture();
        let predicate_type = CoreType::arrow(fixture.nat.clone(), CoreType::Prop);
        let statement = CoreTerm::forall(
            predicate_type,
            CoreTerm::forall(
                fixture.nat.clone(),
                CoreTerm::apply(CoreTerm::Bound(1), CoreTerm::Bound(0)),
            ),
        );
        assert_eq!(
            classify(&fixture, &TermContext::new(), &statement),
            StatementFragment::HigherOrder
        );
    }

    #[test]
    fn predicate_values_and_partial_applications_are_higher_order() {
        let fixture = fixture();
        let predicate_type = CoreType::arrow(fixture.nat.clone(), CoreType::Prop);
        let partial = CoreTerm::apply(
            CoreTerm::Constant(fixture.relation),
            CoreTerm::Constant(fixture.a),
        );
        let statement = CoreTerm::equality(predicate_type, partial.clone(), partial);
        assert_eq!(
            classify(&fixture, &TermContext::new(), &statement),
            StatementFragment::HigherOrder
        );
    }

    #[test]
    fn a_fully_applied_symbol_with_a_predicate_argument_is_higher_order() {
        let mut fixture = fixture();
        let predicate_type = CoreType::arrow(fixture.nat.clone(), CoreType::Prop);
        let higher_order_consumer = fixture
            .constants
            .declare(
                &fixture.types,
                "holds_for_all",
                CoreType::arrow(predicate_type, CoreType::Prop),
            )
            .expect("higher-order consumer");
        let statement = CoreTerm::apply(
            CoreTerm::Constant(higher_order_consumer),
            CoreTerm::Constant(fixture.predicate),
        );
        assert_eq!(
            classify(&fixture, &TermContext::new(), &statement),
            StatementFragment::HigherOrder
        );
    }

    #[test]
    fn explicit_polymorphic_instances_are_classified_from_their_type_arguments() {
        let mut fixture = fixture();
        let parameter = TypeParameter::any(50);
        let generic_predicate = fixture
            .constants
            .declare_polymorphic(
                &fixture.types,
                "generic_predicate",
                vec![parameter],
                CoreType::arrow(CoreType::Parameter(parameter), CoreType::Prop),
            )
            .expect("generic predicate");

        let nat_instance = CoreTerm::apply(
            CoreTerm::instantiate_constant(generic_predicate, vec![fixture.nat.clone()]),
            CoreTerm::Constant(fixture.a),
        );
        assert_eq!(
            classify(&fixture, &TermContext::new(), &nat_instance),
            StatementFragment::FirstOrder
        );

        let predicate_type = CoreType::arrow(fixture.nat.clone(), CoreType::Prop);
        let predicate_instance = CoreTerm::apply(
            CoreTerm::instantiate_constant(generic_predicate, vec![predicate_type]),
            CoreTerm::Constant(fixture.predicate),
        );
        assert_eq!(
            classify(&fixture, &TermContext::new(), &predicate_instance),
            StatementFragment::HigherOrder
        );
    }

    #[test]
    fn inductive_types_and_recursive_symbols_raise_the_fragment() {
        let fixture = fixture();
        let list_statement = CoreTerm::forall(fixture.list_nat.clone(), CoreTerm::Truth);
        assert_eq!(
            classify(&fixture, &TermContext::new(), &list_statement),
            StatementFragment::FirstOrderInductive
        );

        let recursive_statement = CoreTerm::apply(
            CoreTerm::Constant(fixture.recursive_predicate),
            CoreTerm::Constant(fixture.a),
        );
        assert_eq!(
            classify(&fixture, &TermContext::new(), &recursive_statement),
            StatementFragment::FirstOrderInductive
        );
    }

    #[test]
    fn type_parameter_class_is_respected_by_statement_classification() {
        let fixture = fixture();
        let first_order = CoreType::Parameter(TypeParameter::first_order(0));
        let any = CoreType::Parameter(TypeParameter::any(1));
        assert_eq!(
            classify(
                &fixture,
                &TermContext::new(),
                &CoreTerm::forall(first_order, CoreTerm::Truth),
            ),
            StatementFragment::FirstOrder
        );
        assert_eq!(
            classify(
                &fixture,
                &TermContext::new(),
                &CoreTerm::forall(any, CoreTerm::Truth),
            ),
            StatementFragment::HigherOrder
        );
    }

    #[test]
    fn non_propositions_cannot_be_classified_as_statements() {
        let fixture = fixture();
        let error = classify_statement(
            &fixture.types,
            &fixture.constants,
            &TermContext::new(),
            &fixture.metadata,
            &CoreTerm::Constant(fixture.a),
        )
        .expect_err("individual is not a proposition");
        assert!(error.message.contains("must have type `Prop`"));
    }

    #[test]
    fn receipts_union_features_and_dependencies_transitively() {
        let axiom =
            DeclarationReceipt::trusted_axiom(DeclarationId(1), StatementFragment::FirstOrder);
        let incomplete = DeclarationReceipt::incomplete(
            DeclarationId(2),
            StatementFragment::FirstOrderInductive,
            [ProofFeature::Induction],
            [&axiom],
        );
        let middle = DeclarationReceipt::checked(
            DeclarationId(3),
            StatementFragment::FirstOrder,
            [ProofFeature::Classical],
            [&incomplete],
        );
        let leaf = DeclarationReceipt::checked(
            DeclarationId(4),
            StatementFragment::Prop,
            [],
            [&middle, &middle],
        );

        assert_eq!(
            leaf.proof().direct_dependencies(),
            &BTreeSet::from([DeclarationId(3)])
        );
        assert_eq!(
            leaf.proof().transitive_dependencies(),
            &BTreeSet::from([DeclarationId(1), DeclarationId(2), DeclarationId(3)])
        );
        assert_eq!(
            leaf.proof().transitive_features(),
            &BTreeSet::from([ProofFeature::Classical, ProofFeature::Induction])
        );
        assert_eq!(
            leaf.proof().axiom_dependencies(),
            &BTreeSet::from([DeclarationId(1)])
        );
        assert_eq!(
            leaf.proof().incomplete_dependencies(),
            &BTreeSet::from([DeclarationId(2)])
        );
        assert_eq!(
            leaf.proof().required_fragment(),
            StatementFragment::FirstOrderInductive
        );
    }

    #[test]
    fn a_hol_lemma_cannot_be_laundered_through_a_fol_statement() {
        let hol_lemma = DeclarationReceipt::checked(
            DeclarationId(10),
            StatementFragment::HigherOrder,
            [ProofFeature::HigherOrderAbstraction],
            [],
        );
        let fol_facade = DeclarationReceipt::checked(
            DeclarationId(11),
            StatementFragment::FirstOrder,
            [],
            [&hol_lemma],
        );
        let violations = ReceiptPolicy::new(TeachingProfile::FirstOrder).check(&fol_facade);

        assert!(
            violations.contains(&PolicyViolation::DependencyFragmentExceeds {
                actual: StatementFragment::HigherOrder,
                maximum: StatementFragment::FirstOrder,
            })
        );
        assert!(violations.contains(&PolicyViolation::FeatureNotAllowed(
            ProofFeature::HigherOrderAbstraction
        )));
        assert_eq!(
            fol_facade.proof().required_fragment(),
            StatementFragment::HigherOrder
        );
    }

    #[test]
    fn constructive_hol_does_not_silently_allow_strong_principles() {
        let declaration = DeclarationReceipt::checked(
            DeclarationId(20),
            StatementFragment::HigherOrder,
            [
                ProofFeature::HigherOrderInstantiation,
                ProofFeature::Classical,
                ProofFeature::FunctionExtensionality,
                ProofFeature::Choice,
            ],
            [],
        );
        let mut policy = ReceiptPolicy::new(TeachingProfile::HigherOrder);
        let initial = policy.check(&declaration);
        assert_eq!(
            initial,
            vec![
                PolicyViolation::FeatureNotAllowed(ProofFeature::Classical),
                PolicyViolation::FeatureNotAllowed(ProofFeature::FunctionExtensionality),
                PolicyViolation::FeatureNotAllowed(ProofFeature::Choice),
            ]
        );

        policy.allow_classical();
        policy.allow_extensionality();
        policy.allow_choice();
        assert!(policy.check(&declaration).is_empty());
    }

    #[test]
    fn trust_incompleteness_and_dependency_allowlists_are_transitive() {
        let axiom =
            DeclarationReceipt::trusted_axiom(DeclarationId(30), StatementFragment::FirstOrder);
        let incomplete = DeclarationReceipt::incomplete(
            DeclarationId(31),
            StatementFragment::FirstOrder,
            [],
            [&axiom],
        );
        let theorem = DeclarationReceipt::checked(
            DeclarationId(32),
            StatementFragment::FirstOrder,
            [],
            [&incomplete],
        );
        let mut policy = ReceiptPolicy::new(TeachingProfile::FirstOrder);
        policy.restrict_dependencies([DeclarationId(31)]);
        let violations = policy.check(&theorem);
        assert!(violations.contains(&PolicyViolation::TrustedAxiomNotAllowed(DeclarationId(30))));
        assert!(violations.contains(&PolicyViolation::IncompleteNotAllowed(DeclarationId(31))));
        assert!(violations.contains(&PolicyViolation::DependencyNotAllowed(DeclarationId(30))));

        policy.allow_axiom(DeclarationId(30));
        policy.allow_incomplete();
        policy.restrict_dependencies([DeclarationId(30), DeclarationId(31)]);
        assert!(policy.check(&theorem).is_empty());
    }

    #[test]
    fn an_induction_profile_allows_induction_but_not_classical_reasoning() {
        let theorem = DeclarationReceipt::checked(
            DeclarationId(40),
            StatementFragment::FirstOrderInductive,
            [ProofFeature::Induction, ProofFeature::Classical],
            [],
        );
        let violations = ReceiptPolicy::new(TeachingProfile::FirstOrderInductive).check(&theorem);
        assert_eq!(
            violations,
            vec![PolicyViolation::FeatureNotAllowed(ProofFeature::Classical)]
        );
    }
}
