//! Structurally terminating definitions over checked inductive datatypes.
//!
//! A branch never receives the recursive function itself. It receives already
//! computed recursive results only for fields that the datatype checker marked
//! as direct recursive subdata. This makes the first termination criterion
//! syntactic, local, and deliberately less expressive than general recursion.

use std::collections::HashMap;
use std::fmt;

use super::inductive::{InductiveError, InductiveSignature};
use super::terms::{
    infer_type, ConstantId, CoreTerm, StructuralReduction, StructuralReductionArm, TermContext,
    TermError, TermSignature,
};
use super::types::{CoreType, TypeConstructorId, TypeError, TypeParameter, TypeSignature};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructuralArmSpec {
    pub constructor: ConstantId,
    pub body: CoreTerm,
}

impl StructuralArmSpec {
    pub fn new(constructor: ConstantId, body: CoreTerm) -> Self {
        Self { constructor, body }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructuralDefinitionSpec {
    pub name: String,
    pub type_parameters: Vec<TypeParameter>,
    pub datatype: TypeConstructorId,
    pub datatype_arguments: Vec<CoreType>,
    /// Position of the datatype argument among all source arguments.
    pub recursive_argument_index: usize,
    /// Nonrecursive arguments in source order, with the datatype argument
    /// omitted.
    pub fixed_parameter_types: Vec<CoreType>,
    pub result_type: CoreType,
    pub arms: Vec<StructuralArmSpec>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructuralDefinition {
    pub name: String,
    pub constant: ConstantId,
    pub type_parameters: Vec<TypeParameter>,
    pub datatype: TypeConstructorId,
    pub datatype_arguments: Vec<CoreType>,
    pub recursive_argument_index: usize,
    pub fixed_parameter_types: Vec<CoreType>,
    pub result_type: CoreType,
    pub arms: Vec<StructuralArmSpec>,
}

/// De Bruijn layout for a checked branch, nearest binder first:
/// constructor fields, recursive results, then fixed definition arguments.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StructuralArmLayout {
    field_count: usize,
    recursive_result_count: usize,
    fixed_parameter_count: usize,
}

impl StructuralArmLayout {
    pub const fn new(
        field_count: usize,
        recursive_result_count: usize,
        fixed_parameter_count: usize,
    ) -> Self {
        Self {
            field_count,
            recursive_result_count,
            fixed_parameter_count,
        }
    }

    pub fn field(self, index: usize) -> Option<CoreTerm> {
        (index < self.field_count).then(|| CoreTerm::Bound(index as u32))
    }

    pub fn recursive_result(self, index: usize) -> Option<CoreTerm> {
        (index < self.recursive_result_count)
            .then(|| CoreTerm::Bound((self.field_count + index) as u32))
    }

    pub fn fixed_parameter(self, index: usize) -> Option<CoreTerm> {
        (index < self.fixed_parameter_count).then(|| {
            CoreTerm::Bound((self.field_count + self.recursive_result_count + index) as u32)
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecursionError {
    pub message: String,
}

impl RecursionError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for RecursionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for RecursionError {}

impl From<TypeError> for RecursionError {
    fn from(error: TypeError) -> Self {
        Self::new(error.message)
    }
}

impl From<TermError> for RecursionError {
    fn from(error: TermError) -> Self {
        Self::new(error.message)
    }
}

impl From<InductiveError> for RecursionError {
    fn from(error: InductiveError) -> Self {
        Self::new(error.message)
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RecursionSignature {
    definitions: Vec<StructuralDefinition>,
    by_constant: HashMap<ConstantId, usize>,
}

impl RecursionSignature {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn declare(
        &mut self,
        types: &TypeSignature,
        constants: &mut TermSignature,
        inductives: &InductiveSignature,
        spec: StructuralDefinitionSpec,
    ) -> Result<ConstantId, RecursionError> {
        types.validate_scheme(&spec.type_parameters, &CoreType::Prop)?;
        let datatype_declaration = inductives.declaration(spec.datatype).ok_or_else(|| {
            RecursionError::new(format!(
                "type constructor `{}` is not a checked inductive datatype",
                spec.datatype.0
            ))
        })?;
        let datatype_type = CoreType::constructor(spec.datatype, spec.datatype_arguments.clone());
        types.validate_scheme(&spec.type_parameters, &datatype_type)?;
        for parameter_type in &spec.fixed_parameter_types {
            types.validate_scheme(&spec.type_parameters, parameter_type)?;
        }
        types.validate_scheme(&spec.type_parameters, &spec.result_type)?;
        if spec.recursive_argument_index > spec.fixed_parameter_types.len() {
            return Err(RecursionError::new(format!(
                "structural definition `{}` has recursive argument index {}, but only {} total argument(s)",
                spec.name,
                spec.recursive_argument_index,
                spec.fixed_parameter_types.len() + 1
            )));
        }

        if spec.arms.len() != datatype_declaration.constructors.len() {
            return Err(RecursionError::new(format!(
                "structural definition `{}` needs {} arm(s), but got {}",
                spec.name,
                datatype_declaration.constructors.len(),
                spec.arms.len()
            )));
        }

        let proposed_id = constants.next_constant_id()?;
        let mut reduction_arms = Vec::with_capacity(spec.arms.len());
        for (arm, constructor) in spec.arms.iter().zip(&datatype_declaration.constructors) {
            if arm.constructor != constructor.constant {
                return Err(RecursionError::new(format!(
                    "structural definition `{}` arm for constructor `{}` is out of order; expected `{}`",
                    spec.name, arm.constructor.0, constructor.constant.0
                )));
            }
            if term_mentions_constant(&arm.body, proposed_id) {
                return Err(RecursionError::new(format!(
                    "structural definition `{}` calls itself directly; branches may use only the supplied recursive-result binders",
                    spec.name
                )));
            }

            let instantiated = inductives.instantiate_constructor(
                types,
                constructor.constant,
                &spec.datatype_arguments,
            )?;
            let mut binder_types = instantiated.field_types.clone();
            binder_types.extend(
                instantiated
                    .recursive_fields
                    .iter()
                    .map(|_| spec.result_type.clone()),
            );
            binder_types.extend(spec.fixed_parameter_types.iter().cloned());
            let context = context_from_nearest(&binder_types);
            let actual = infer_type(types, constants, &context, &arm.body).map_err(|error| {
                RecursionError::new(format!(
                    "structural definition `{}` arm for constructor `{}` is ill-typed: {}",
                    spec.name, constructor.name, error.message
                ))
            })?;
            if actual != spec.result_type {
                return Err(RecursionError::new(format!(
                    "structural definition `{}` arm for constructor `{}` has type `{actual:?}`, but expected `{:?}`",
                    spec.name, constructor.name, spec.result_type
                )));
            }
            reduction_arms.push(StructuralReductionArm {
                constructor: constructor.constant,
                field_count: instantiated.field_types.len(),
                recursive_fields: instantiated.recursive_fields,
                binder_types,
                body: arm.body.clone(),
            });
        }

        let mut argument_types = spec.fixed_parameter_types.clone();
        argument_types.insert(spec.recursive_argument_index, datatype_type);
        let definition_type = argument_types
            .iter()
            .rev()
            .fold(spec.result_type.clone(), |result, parameter| {
                CoreType::arrow(parameter.clone(), result)
            });
        let mut staged_constants = constants.clone();
        let constant = staged_constants.declare_polymorphic(
            types,
            spec.name.clone(),
            spec.type_parameters.clone(),
            definition_type,
        )?;
        if constant != proposed_id || self.by_constant.contains_key(&constant) {
            return Err(RecursionError::new(
                "recursion and term signatures do not share the same declaration history",
            ));
        }
        staged_constants.register_structural_reduction(
            constant,
            StructuralReduction {
                type_parameters: spec.type_parameters.clone(),
                fixed_parameter_count: spec.fixed_parameter_types.len(),
                recursive_argument_index: spec.recursive_argument_index,
                arms: reduction_arms,
            },
        )?;

        let definition_index = self.definitions.len();
        self.by_constant.insert(constant, definition_index);
        self.definitions.push(StructuralDefinition {
            name: spec.name,
            constant,
            type_parameters: spec.type_parameters,
            datatype: spec.datatype,
            datatype_arguments: spec.datatype_arguments,
            recursive_argument_index: spec.recursive_argument_index,
            fixed_parameter_types: spec.fixed_parameter_types,
            result_type: spec.result_type,
            arms: spec.arms,
        });
        *constants = staged_constants;
        Ok(constant)
    }

    pub fn definition(&self, id: ConstantId) -> Option<&StructuralDefinition> {
        self.by_constant
            .get(&id)
            .and_then(|index| self.definitions.get(*index))
    }
}

fn context_from_nearest(types: &[CoreType]) -> TermContext {
    types.iter().rev().fold(TermContext::new(), |context, ty| {
        context.with_bound(ty.clone())
    })
}

fn term_mentions_constant(term: &CoreTerm, sought: ConstantId) -> bool {
    match term {
        CoreTerm::Bound(_)
        | CoreTerm::Truth
        | CoreTerm::Falsity
        | CoreTerm::EmptySet { .. }
        | CoreTerm::UniverseSet { .. } => false,
        CoreTerm::Constant(id) => *id == sought,
        CoreTerm::TypeApplication { constant, .. } => *constant == sought,
        CoreTerm::Lambda { body, .. }
        | CoreTerm::Forall { body, .. }
        | CoreTerm::Exists { body, .. }
        | CoreTerm::First(body)
        | CoreTerm::Second(body)
        | CoreTerm::SingletonSet(body)
        | CoreTerm::SetComplement(body)
        | CoreTerm::Powerset { set: body, .. }
        | CoreTerm::SetBuilder { body, .. } => term_mentions_constant(body, sought),
        CoreTerm::Apply { function, argument }
        | CoreTerm::Pair(function, argument)
        | CoreTerm::SetUnion(function, argument)
        | CoreTerm::SetIntersection(function, argument)
        | CoreTerm::SetDifference(function, argument)
        | CoreTerm::SetProduct(function, argument)
        | CoreTerm::And(function, argument)
        | CoreTerm::Or(function, argument)
        | CoreTerm::Implies(function, argument) => {
            term_mentions_constant(function, sought) || term_mentions_constant(argument, sought)
        }
        CoreTerm::Equality { left, right, .. } => {
            term_mentions_constant(left, sought) || term_mentions_constant(right, sought)
        }
        CoreTerm::Membership { element, set, .. } => {
            term_mentions_constant(element, sought) || term_mentions_constant(set, sought)
        }
        CoreTerm::Subset { left, right, .. } => {
            term_mentions_constant(left, sought) || term_mentions_constant(right, sought)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::inductive::{InductiveConstructorSpec, InductiveFieldType, InductiveSpec};
    use crate::hol::terms::{normalize, ConstantId};

    struct Fixture {
        types: TypeSignature,
        constants: TermSignature,
        inductives: InductiveSignature,
        recursion: RecursionSignature,
        nat: CoreType,
        zero: ConstantId,
        succ: ConstantId,
        list: TypeConstructorId,
        nil: ConstantId,
        cons: ConstantId,
        parameter: TypeParameter,
    }

    fn fixture() -> Fixture {
        let mut types = TypeSignature::new();
        let nat_id = types.declare("Nat", 0, true).expect("Nat");
        let nat = CoreType::constructor(nat_id, Vec::new());
        let mut constants = TermSignature::new();
        let zero = constants
            .declare(&types, "zero", nat.clone())
            .expect("zero");
        let succ = constants
            .declare(&types, "succ", CoreType::arrow(nat.clone(), nat.clone()))
            .expect("succ");
        let parameter = TypeParameter::any(0);
        let mut inductives = InductiveSignature::new();
        let list = inductives
            .declare(
                &mut types,
                &mut constants,
                InductiveSpec::new(
                    "List",
                    vec![parameter],
                    vec![
                        InductiveConstructorSpec::new("nil", Vec::new()),
                        InductiveConstructorSpec::new(
                            "cons",
                            vec![
                                InductiveFieldType::existing(CoreType::Parameter(parameter)),
                                InductiveFieldType::Recursive,
                            ],
                        ),
                    ],
                ),
            )
            .expect("List");
        let nil = constants.resolve("nil").expect("nil");
        let cons = constants.resolve("cons").expect("cons");
        Fixture {
            types,
            constants,
            inductives,
            recursion: RecursionSignature::new(),
            nat,
            zero,
            succ,
            list,
            nil,
            cons,
            parameter,
        }
    }

    fn nil(fixture: &Fixture) -> CoreTerm {
        CoreTerm::instantiate_constant(fixture.nil, vec![fixture.nat.clone()])
    }

    fn cons(fixture: &Fixture, head: CoreTerm, tail: CoreTerm) -> CoreTerm {
        CoreTerm::apply(
            CoreTerm::apply(
                CoreTerm::instantiate_constant(fixture.cons, vec![fixture.nat.clone()]),
                head,
            ),
            tail,
        )
    }

    fn declare_length(fixture: &mut Fixture) -> ConstantId {
        let cons_layout = StructuralArmLayout::new(2, 1, 0);
        fixture
            .recursion
            .declare(
                &fixture.types,
                &mut fixture.constants,
                &fixture.inductives,
                StructuralDefinitionSpec {
                    name: "length".to_string(),
                    type_parameters: vec![fixture.parameter],
                    datatype: fixture.list,
                    datatype_arguments: vec![CoreType::Parameter(fixture.parameter)],
                    fixed_parameter_types: Vec::new(),
                    recursive_argument_index: 0,
                    result_type: fixture.nat.clone(),
                    arms: vec![
                        StructuralArmSpec::new(fixture.nil, CoreTerm::Constant(fixture.zero)),
                        StructuralArmSpec::new(
                            fixture.cons,
                            CoreTerm::apply(
                                CoreTerm::Constant(fixture.succ),
                                cons_layout.recursive_result(0).expect("recursive result"),
                            ),
                        ),
                    ],
                },
            )
            .expect("length")
    }

    #[test]
    fn structural_recursion_computes_on_constructor_subdata() {
        let mut fixture = fixture();
        let length = declare_length(&mut fixture);
        let list = cons(
            &fixture,
            CoreTerm::Constant(fixture.zero),
            cons(&fixture, CoreTerm::Constant(fixture.zero), nil(&fixture)),
        );
        let call = CoreTerm::apply(
            CoreTerm::instantiate_constant(length, vec![fixture.nat.clone()]),
            list,
        );
        let expected = CoreTerm::apply(
            CoreTerm::Constant(fixture.succ),
            CoreTerm::apply(
                CoreTerm::Constant(fixture.succ),
                CoreTerm::Constant(fixture.zero),
            ),
        );
        assert_eq!(
            normalize(
                &fixture.types,
                &fixture.constants,
                &TermContext::new(),
                &call,
            ),
            Ok(expected)
        );
        assert!(fixture.recursion.definition(length).is_some());
    }

    #[test]
    fn recursive_predicates_compute_to_propositions() {
        let mut fixture = fixture();
        let predicate = fixture
            .constants
            .declare(
                &fixture.types,
                "P",
                CoreType::arrow(fixture.nat.clone(), CoreType::Prop),
            )
            .expect("P");
        let cons_layout = StructuralArmLayout::new(2, 1, 1);
        let all = fixture
            .recursion
            .declare(
                &fixture.types,
                &mut fixture.constants,
                &fixture.inductives,
                StructuralDefinitionSpec {
                    name: "All".to_string(),
                    type_parameters: vec![fixture.parameter],
                    datatype: fixture.list,
                    datatype_arguments: vec![CoreType::Parameter(fixture.parameter)],
                    fixed_parameter_types: vec![CoreType::arrow(
                        CoreType::Parameter(fixture.parameter),
                        CoreType::Prop,
                    )],
                    recursive_argument_index: 1,
                    result_type: CoreType::Prop,
                    arms: vec![
                        StructuralArmSpec::new(fixture.nil, CoreTerm::Truth),
                        StructuralArmSpec::new(
                            fixture.cons,
                            CoreTerm::and(
                                CoreTerm::apply(
                                    cons_layout.fixed_parameter(0).expect("predicate"),
                                    cons_layout.field(0).expect("head"),
                                ),
                                cons_layout.recursive_result(0).expect("tail result"),
                            ),
                        ),
                    ],
                },
            )
            .expect("All");
        let singleton = cons(&fixture, CoreTerm::Constant(fixture.zero), nil(&fixture));
        let call = CoreTerm::apply(
            CoreTerm::apply(
                CoreTerm::instantiate_constant(all, vec![fixture.nat.clone()]),
                CoreTerm::Constant(predicate),
            ),
            singleton,
        );
        assert_eq!(
            normalize(
                &fixture.types,
                &fixture.constants,
                &TermContext::new(),
                &call,
            ),
            Ok(CoreTerm::and(
                CoreTerm::apply(
                    CoreTerm::Constant(predicate),
                    CoreTerm::Constant(fixture.zero),
                ),
                CoreTerm::Truth,
            ))
        );
    }

    #[test]
    fn first_recursive_argument_reduces_and_avoids_capture() {
        let mut fixture = fixture();
        let default = CoreType::Parameter(fixture.parameter);
        let definition = fixture
            .recursion
            .declare(
                &fixture.types,
                &mut fixture.constants,
                &fixture.inductives,
                StructuralDefinitionSpec {
                    name: "head_or".to_string(),
                    type_parameters: vec![fixture.parameter],
                    datatype: fixture.list,
                    datatype_arguments: vec![CoreType::Parameter(fixture.parameter)],
                    fixed_parameter_types: vec![default.clone()],
                    recursive_argument_index: 0,
                    result_type: default,
                    arms: vec![
                        StructuralArmSpec::new(
                            fixture.nil,
                            StructuralArmLayout::new(0, 0, 1)
                                .fixed_parameter(0)
                                .expect("default"),
                        ),
                        StructuralArmSpec::new(
                            fixture.cons,
                            StructuralArmLayout::new(2, 1, 1).field(0).expect("head"),
                        ),
                    ],
                },
            )
            .expect("head_or");
        let context = TermContext::new().with_bound(fixture.nat.clone());
        let call = CoreTerm::apply(
            CoreTerm::apply(
                CoreTerm::instantiate_constant(definition, vec![fixture.nat.clone()]),
                nil(&fixture),
            ),
            CoreTerm::Bound(0),
        );
        assert_eq!(
            normalize(&fixture.types, &fixture.constants, &context, &call),
            Ok(CoreTerm::Bound(0))
        );
        assert_eq!(
            fixture
                .recursion
                .definition(definition)
                .expect("stored head_or")
                .recursive_argument_index,
            0
        );
    }

    #[test]
    fn recursive_calls_preserve_a_first_recursive_argument_position() {
        let mut fixture = fixture();
        let list_parameter =
            CoreType::constructor(fixture.list, vec![CoreType::Parameter(fixture.parameter)]);
        let nil_layout = StructuralArmLayout::new(0, 0, 1);
        let cons_layout = StructuralArmLayout::new(2, 1, 1);
        let append = fixture
            .recursion
            .declare(
                &fixture.types,
                &mut fixture.constants,
                &fixture.inductives,
                StructuralDefinitionSpec {
                    name: "append_first".to_string(),
                    type_parameters: vec![fixture.parameter],
                    datatype: fixture.list,
                    datatype_arguments: vec![CoreType::Parameter(fixture.parameter)],
                    fixed_parameter_types: vec![list_parameter.clone()],
                    recursive_argument_index: 0,
                    result_type: list_parameter,
                    arms: vec![
                        StructuralArmSpec::new(
                            fixture.nil,
                            nil_layout.fixed_parameter(0).expect("right list"),
                        ),
                        StructuralArmSpec::new(
                            fixture.cons,
                            CoreTerm::apply(
                                CoreTerm::apply(
                                    CoreTerm::instantiate_constant(
                                        fixture.cons,
                                        vec![CoreType::Parameter(fixture.parameter)],
                                    ),
                                    cons_layout.field(0).expect("head"),
                                ),
                                cons_layout.recursive_result(0).expect("appended tail"),
                            ),
                        ),
                    ],
                },
            )
            .expect("append with its recursive list first");
        let singleton = cons(&fixture, CoreTerm::Constant(fixture.zero), nil(&fixture));
        let call = CoreTerm::apply(
            CoreTerm::apply(
                CoreTerm::instantiate_constant(append, vec![fixture.nat.clone()]),
                singleton.clone(),
            ),
            singleton,
        );
        let expected = cons(
            &fixture,
            CoreTerm::Constant(fixture.zero),
            cons(&fixture, CoreTerm::Constant(fixture.zero), nil(&fixture)),
        );
        assert_eq!(
            normalize(
                &fixture.types,
                &fixture.constants,
                &TermContext::new(),
                &call,
            ),
            Ok(expected)
        );
    }

    #[test]
    fn invalid_recursive_argument_positions_are_transactional() {
        let mut fixture = fixture();
        let error = fixture
            .recursion
            .declare(
                &fixture.types,
                &mut fixture.constants,
                &fixture.inductives,
                StructuralDefinitionSpec {
                    name: "bad_position".to_string(),
                    type_parameters: vec![fixture.parameter],
                    datatype: fixture.list,
                    datatype_arguments: vec![CoreType::Parameter(fixture.parameter)],
                    fixed_parameter_types: vec![CoreType::Parameter(fixture.parameter)],
                    recursive_argument_index: 2,
                    result_type: CoreType::Parameter(fixture.parameter),
                    arms: vec![
                        StructuralArmSpec::new(fixture.nil, CoreTerm::Bound(0)),
                        StructuralArmSpec::new(fixture.cons, CoreTerm::Bound(0)),
                    ],
                },
            )
            .expect_err("position must be within the source argument list");
        assert!(error.message.contains("recursive argument index 2"));
        assert_eq!(fixture.constants.resolve("bad_position"), None);
    }

    #[test]
    fn recursive_calls_on_arbitrary_arguments_are_rejected() {
        let mut fixture = fixture();
        let proposed = fixture.constants.next_constant_id().expect("next id");
        let malicious_call = CoreTerm::apply(
            CoreTerm::instantiate_constant(proposed, vec![CoreType::Parameter(fixture.parameter)]),
            StructuralArmLayout::new(2, 1, 0).field(1).expect("tail"),
        );
        let error = fixture
            .recursion
            .declare(
                &fixture.types,
                &mut fixture.constants,
                &fixture.inductives,
                StructuralDefinitionSpec {
                    name: "bad_length".to_string(),
                    type_parameters: vec![fixture.parameter],
                    datatype: fixture.list,
                    datatype_arguments: vec![CoreType::Parameter(fixture.parameter)],
                    fixed_parameter_types: Vec::new(),
                    recursive_argument_index: 0,
                    result_type: fixture.nat.clone(),
                    arms: vec![
                        StructuralArmSpec::new(fixture.nil, CoreTerm::Constant(fixture.zero)),
                        StructuralArmSpec::new(fixture.cons, malicious_call),
                    ],
                },
            )
            .expect_err("direct self call must fail");
        assert!(error.message.contains("calls itself directly"));
        assert_eq!(fixture.constants.resolve("bad_length"), None);
    }

    #[test]
    fn ill_typed_arm_and_missing_arm_do_not_declare_a_constant() {
        let mut fixture = fixture();
        let missing = fixture
            .recursion
            .declare(
                &fixture.types,
                &mut fixture.constants,
                &fixture.inductives,
                StructuralDefinitionSpec {
                    name: "missing".to_string(),
                    type_parameters: vec![fixture.parameter],
                    datatype: fixture.list,
                    datatype_arguments: vec![CoreType::Parameter(fixture.parameter)],
                    fixed_parameter_types: Vec::new(),
                    recursive_argument_index: 0,
                    result_type: fixture.nat.clone(),
                    arms: vec![StructuralArmSpec::new(
                        fixture.nil,
                        CoreTerm::Constant(fixture.zero),
                    )],
                },
            )
            .expect_err("missing cons arm");
        assert!(missing.message.contains("needs 2 arm"));
        assert_eq!(fixture.constants.resolve("missing"), None);

        let wrong_type = fixture
            .recursion
            .declare(
                &fixture.types,
                &mut fixture.constants,
                &fixture.inductives,
                StructuralDefinitionSpec {
                    name: "wrong_type".to_string(),
                    type_parameters: vec![fixture.parameter],
                    datatype: fixture.list,
                    datatype_arguments: vec![CoreType::Parameter(fixture.parameter)],
                    fixed_parameter_types: Vec::new(),
                    recursive_argument_index: 0,
                    result_type: fixture.nat.clone(),
                    arms: vec![
                        StructuralArmSpec::new(fixture.nil, CoreTerm::Truth),
                        StructuralArmSpec::new(
                            fixture.cons,
                            StructuralArmLayout::new(2, 1, 0)
                                .recursive_result(0)
                                .expect("recursive result"),
                        ),
                    ],
                },
            )
            .expect_err("nil arm is Prop, not Nat");
        assert!(wrong_type.message.contains("has type"));
        assert_eq!(fixture.constants.resolve("wrong_type"), None);
    }

    #[test]
    fn structural_calls_remain_stuck_on_variables() {
        let mut fixture = fixture();
        let length = declare_length(&mut fixture);
        let list_nat = CoreType::constructor(fixture.list, vec![fixture.nat.clone()]);
        let context = TermContext::new().with_bound(list_nat);
        let call = CoreTerm::apply(
            CoreTerm::instantiate_constant(length, vec![fixture.nat.clone()]),
            CoreTerm::Bound(0),
        );
        assert_eq!(
            normalize(&fixture.types, &fixture.constants, &context, &call),
            Ok(call)
        );
    }

    #[test]
    fn reduction_substitutes_type_arguments_through_branch_annotations() {
        let mut fixture = fixture();
        let definition = fixture
            .recursion
            .declare(
                &fixture.types,
                &mut fixture.constants,
                &fixture.inductives,
                StructuralDefinitionSpec {
                    name: "head_reflexive".to_string(),
                    type_parameters: vec![fixture.parameter],
                    datatype: fixture.list,
                    datatype_arguments: vec![CoreType::Parameter(fixture.parameter)],
                    fixed_parameter_types: Vec::new(),
                    recursive_argument_index: 0,
                    result_type: CoreType::Prop,
                    arms: vec![
                        StructuralArmSpec::new(fixture.nil, CoreTerm::Truth),
                        StructuralArmSpec::new(
                            fixture.cons,
                            CoreTerm::equality(
                                CoreType::Parameter(fixture.parameter),
                                CoreTerm::Bound(0),
                                CoreTerm::Bound(0),
                            ),
                        ),
                    ],
                },
            )
            .expect("head_reflexive");
        let singleton = cons(&fixture, CoreTerm::Constant(fixture.zero), nil(&fixture));
        let call = CoreTerm::apply(
            CoreTerm::instantiate_constant(definition, vec![fixture.nat.clone()]),
            singleton,
        );
        assert_eq!(
            normalize(
                &fixture.types,
                &fixture.constants,
                &TermContext::new(),
                &call,
            ),
            Ok(CoreTerm::equality(
                fixture.nat,
                CoreTerm::Constant(fixture.zero),
                CoreTerm::Constant(fixture.zero),
            ))
        );
    }
}
