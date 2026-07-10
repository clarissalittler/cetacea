//! Checked parameterized inductive declarations for the HOL spike.
//!
//! The initial implementation intentionally accepts only direct regular
//! recursion. That is enough for lists, paths, finite enumerations, and ordinary
//! trees while keeping positivity and structural-recursion metadata auditable.
//! Nested, mutual, and indexed inductive families remain explicit future work.

use std::collections::{HashMap, HashSet};
use std::fmt;

use super::terms::{ConstantId, TermError, TermSignature};
use super::types::{
    CoreType, FirstOrderStatus, TypeConstructorId, TypeError, TypeParameter, TypeParameterClass,
    TypeParameterId, TypeSignature,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InductiveFieldType {
    /// A type that does not mention the datatype currently being declared.
    Existing(CoreType),
    /// A direct recursive occurrence, elaborated to `C parameters`.
    Recursive,
    /// Available so positivity failures are represented and diagnosed before
    /// lowering. Recursive occurrences nested here are not yet accepted.
    Arrow(Box<InductiveFieldType>, Box<InductiveFieldType>),
    Product(Box<InductiveFieldType>, Box<InductiveFieldType>),
}

impl InductiveFieldType {
    pub fn existing(ty: CoreType) -> Self {
        Self::Existing(ty)
    }

    pub fn arrow(domain: Self, codomain: Self) -> Self {
        Self::Arrow(Box::new(domain), Box::new(codomain))
    }

    pub fn product(left: Self, right: Self) -> Self {
        Self::Product(Box::new(left), Box::new(right))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InductiveConstructorSpec {
    pub name: String,
    pub fields: Vec<InductiveFieldType>,
}

impl InductiveConstructorSpec {
    pub fn new(name: impl Into<String>, fields: Vec<InductiveFieldType>) -> Self {
        Self {
            name: name.into(),
            fields,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InductiveSpec {
    pub name: String,
    pub type_parameters: Vec<TypeParameter>,
    pub constructors: Vec<InductiveConstructorSpec>,
}

impl InductiveSpec {
    pub fn new(
        name: impl Into<String>,
        type_parameters: Vec<TypeParameter>,
        constructors: Vec<InductiveConstructorSpec>,
    ) -> Self {
        Self {
            name: name.into(),
            type_parameters,
            constructors,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InductiveConstructor {
    pub name: String,
    pub constant: ConstantId,
    pub field_types: Vec<CoreType>,
    pub recursive_fields: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InductiveDeclaration {
    pub name: String,
    pub type_constructor: TypeConstructorId,
    pub type_parameters: Vec<TypeParameter>,
    pub preserves_first_order: bool,
    pub constructors: Vec<InductiveConstructor>,
}

impl InductiveDeclaration {
    pub fn schematic_type(&self) -> CoreType {
        CoreType::constructor(
            self.type_constructor,
            self.type_parameters
                .iter()
                .copied()
                .map(CoreType::Parameter)
                .collect(),
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstantiatedConstructor {
    pub constant: ConstantId,
    pub field_types: Vec<CoreType>,
    pub result_type: CoreType,
    pub recursive_fields: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InductiveError {
    pub message: String,
}

impl InductiveError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for InductiveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for InductiveError {}

impl From<TypeError> for InductiveError {
    fn from(error: TypeError) -> Self {
        Self::new(error.message)
    }
}

impl From<TermError> for InductiveError {
    fn from(error: TermError) -> Self {
        Self::new(error.message)
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct InductiveSignature {
    declarations: Vec<InductiveDeclaration>,
    by_type: HashMap<TypeConstructorId, usize>,
    by_constructor: HashMap<ConstantId, (usize, usize)>,
}

impl InductiveSignature {
    pub fn new() -> Self {
        Self::default()
    }

    /// Check and atomically register an inductive declaration.
    ///
    /// `TypeSignature` and `TermSignature` are cloned while the declaration is
    /// staged. Any name, type, positivity, or constructor failure leaves all
    /// three signatures unchanged.
    pub fn declare(
        &mut self,
        types: &mut TypeSignature,
        constants: &mut TermSignature,
        spec: InductiveSpec,
    ) -> Result<TypeConstructorId, InductiveError> {
        types.validate_scheme(&spec.type_parameters, &CoreType::Prop)?;
        validate_constructor_names(&spec)?;

        for constructor in &spec.constructors {
            for field in &constructor.fields {
                validate_field_type(types, &spec.type_parameters, field, true, 0).map_err(
                    |error| {
                        InductiveError::new(format!(
                            "constructor `{}` of `{}` has invalid field type: {}",
                            constructor.name, spec.name, error.message
                        ))
                    },
                )?;
            }
        }

        let mut preserves_first_order = true;
        for constructor in &spec.constructors {
            for field in &constructor.fields {
                preserves_first_order &=
                    field_preserves_first_order(types, &spec.type_parameters, field)?;
            }
        }

        let mut staged_types = types.clone();
        let mut staged_constants = constants.clone();
        let type_constructor = staged_types.declare_parameterized(
            spec.name.clone(),
            spec.type_parameters
                .iter()
                .map(|parameter| parameter.class)
                .collect(),
            preserves_first_order,
        )?;
        if self.by_type.contains_key(&type_constructor) {
            return Err(InductiveError::new(
                "inductive and type signatures do not share the same declaration history",
            ));
        }
        let schematic_type = CoreType::constructor(
            type_constructor,
            spec.type_parameters
                .iter()
                .copied()
                .map(CoreType::Parameter)
                .collect(),
        );

        let mut checked_constructors = Vec::with_capacity(spec.constructors.len());
        for constructor in spec.constructors {
            let field_types = constructor
                .fields
                .iter()
                .map(|field| lower_field_type(field, &schematic_type))
                .collect::<Vec<_>>();
            let recursive_fields = constructor
                .fields
                .iter()
                .enumerate()
                .filter_map(|(index, field)| {
                    matches!(field, InductiveFieldType::Recursive).then_some(index)
                })
                .collect::<Vec<_>>();
            let constructor_type = field_types
                .iter()
                .rev()
                .fold(schematic_type.clone(), |result, field| {
                    CoreType::arrow(field.clone(), result)
                });
            let constant = staged_constants.declare_polymorphic(
                &staged_types,
                constructor.name.clone(),
                spec.type_parameters.clone(),
                constructor_type,
            )?;
            if self.by_constructor.contains_key(&constant) {
                return Err(InductiveError::new(
                    "inductive and term signatures do not share the same declaration history",
                ));
            }
            checked_constructors.push(InductiveConstructor {
                name: constructor.name,
                constant,
                field_types,
                recursive_fields,
            });
        }

        let declaration_index = self.declarations.len();
        for (constructor_index, constructor) in checked_constructors.iter().enumerate() {
            self.by_constructor
                .insert(constructor.constant, (declaration_index, constructor_index));
        }
        self.by_type.insert(type_constructor, declaration_index);
        self.declarations.push(InductiveDeclaration {
            name: spec.name,
            type_constructor,
            type_parameters: spec.type_parameters,
            preserves_first_order,
            constructors: checked_constructors,
        });
        *types = staged_types;
        *constants = staged_constants;
        Ok(type_constructor)
    }

    pub fn declaration(&self, id: TypeConstructorId) -> Option<&InductiveDeclaration> {
        self.by_type
            .get(&id)
            .and_then(|index| self.declarations.get(*index))
    }

    pub fn constructor(&self, id: ConstantId) -> Option<&InductiveConstructor> {
        let (declaration, constructor) = *self.by_constructor.get(&id)?;
        self.declarations
            .get(declaration)?
            .constructors
            .get(constructor)
    }

    pub fn constructor_declaration(
        &self,
        id: ConstantId,
    ) -> Option<(&InductiveDeclaration, &InductiveConstructor)> {
        let (declaration, constructor) = *self.by_constructor.get(&id)?;
        let declaration = self.declarations.get(declaration)?;
        Some((declaration, declaration.constructors.get(constructor)?))
    }

    pub fn instantiate_constructor(
        &self,
        types: &TypeSignature,
        id: ConstantId,
        type_arguments: &[CoreType],
    ) -> Result<InstantiatedConstructor, InductiveError> {
        let (declaration_index, constructor_index) = *self
            .by_constructor
            .get(&id)
            .ok_or_else(|| InductiveError::new(format!("unknown constructor id `{}`", id.0)))?;
        let declaration = &self.declarations[declaration_index];
        let constructor = &declaration.constructors[constructor_index];
        let field_types = constructor
            .field_types
            .iter()
            .map(|field| {
                types.instantiate_scheme(&declaration.type_parameters, field, type_arguments)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let result_type = types.instantiate_scheme(
            &declaration.type_parameters,
            &declaration.schematic_type(),
            type_arguments,
        )?;
        Ok(InstantiatedConstructor {
            constant: id,
            field_types,
            result_type,
            recursive_fields: constructor.recursive_fields.clone(),
        })
    }
}

fn validate_constructor_names(spec: &InductiveSpec) -> Result<(), InductiveError> {
    let mut names = HashSet::new();
    for constructor in &spec.constructors {
        if constructor.name == spec.name {
            return Err(InductiveError::new(format!(
                "constructor `{}` cannot reuse datatype name `{}`",
                constructor.name, spec.name
            )));
        }
        if !names.insert(constructor.name.as_str()) {
            return Err(InductiveError::new(format!(
                "datatype `{}` repeats constructor name `{}`",
                spec.name, constructor.name
            )));
        }
    }
    Ok(())
}

fn validate_field_type(
    types: &TypeSignature,
    parameters: &[TypeParameter],
    field: &InductiveFieldType,
    positive: bool,
    depth: usize,
) -> Result<(), InductiveError> {
    match field {
        InductiveFieldType::Existing(ty) => {
            types.validate_scheme(parameters, ty)?;
            Ok(())
        }
        InductiveFieldType::Recursive if !positive => Err(InductiveError::new(
            "the datatype occurs negatively to the left of a function arrow",
        )),
        InductiveFieldType::Recursive if depth > 0 => Err(InductiveError::new(
            "nested recursive occurrences are not supported; use a direct recursive field",
        )),
        InductiveFieldType::Recursive => Ok(()),
        InductiveFieldType::Arrow(domain, codomain) => {
            validate_field_type(types, parameters, domain, !positive, depth + 1)?;
            validate_field_type(types, parameters, codomain, positive, depth + 1)
        }
        InductiveFieldType::Product(left, right) => {
            validate_field_type(types, parameters, left, positive, depth + 1)?;
            validate_field_type(types, parameters, right, positive, depth + 1)
        }
    }
}

fn lower_field_type(field: &InductiveFieldType, recursive_type: &CoreType) -> CoreType {
    match field {
        InductiveFieldType::Existing(ty) => ty.clone(),
        InductiveFieldType::Recursive => recursive_type.clone(),
        InductiveFieldType::Arrow(domain, codomain) => CoreType::arrow(
            lower_field_type(domain, recursive_type),
            lower_field_type(codomain, recursive_type),
        ),
        InductiveFieldType::Product(left, right) => CoreType::product(
            lower_field_type(left, recursive_type),
            lower_field_type(right, recursive_type),
        ),
    }
}

fn field_preserves_first_order(
    types: &TypeSignature,
    parameters: &[TypeParameter],
    field: &InductiveFieldType,
) -> Result<bool, TypeError> {
    match field {
        InductiveFieldType::Recursive => Ok(true),
        InductiveFieldType::Arrow(_, _) => Ok(false),
        InductiveFieldType::Product(left, right) => {
            Ok(field_preserves_first_order(types, parameters, left)?
                && field_preserves_first_order(types, parameters, right)?)
        }
        InductiveFieldType::Existing(ty) => {
            let parameter_ids = parameters
                .iter()
                .map(|parameter| parameter.id)
                .collect::<HashSet<_>>();
            let assumed_first_order = assume_parameters_first_order(ty, &parameter_ids);
            Ok(types.first_order_status(&assumed_first_order)? == FirstOrderStatus::FirstOrder)
        }
    }
}

fn assume_parameters_first_order(ty: &CoreType, parameters: &HashSet<TypeParameterId>) -> CoreType {
    match ty {
        CoreType::Prop => CoreType::Prop,
        CoreType::Parameter(parameter) if parameters.contains(&parameter.id) => {
            CoreType::Parameter(TypeParameter {
                id: parameter.id,
                class: TypeParameterClass::FirstOrder,
            })
        }
        CoreType::Parameter(parameter) => CoreType::Parameter(*parameter),
        CoreType::Constructor { id, arguments } => CoreType::constructor(
            *id,
            arguments
                .iter()
                .map(|argument| assume_parameters_first_order(argument, parameters))
                .collect(),
        ),
        CoreType::Arrow(domain, codomain) => CoreType::arrow(
            assume_parameters_first_order(domain, parameters),
            assume_parameters_first_order(codomain, parameters),
        ),
        CoreType::Product(left, right) => CoreType::product(
            assume_parameters_first_order(left, parameters),
            assume_parameters_first_order(right, parameters),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::terms::{infer_type, CoreTerm, TermContext};

    struct Fixture {
        types: TypeSignature,
        constants: TermSignature,
        inductives: InductiveSignature,
        nat: CoreType,
        zero: ConstantId,
    }

    fn fixture() -> Fixture {
        let mut types = TypeSignature::new();
        let nat_id = types.declare("Nat", 0, true).expect("Nat");
        let nat = CoreType::constructor(nat_id, Vec::new());
        let mut constants = TermSignature::new();
        let zero = constants
            .declare(&types, "zero", nat.clone())
            .expect("zero");
        Fixture {
            types,
            constants,
            inductives: InductiveSignature::new(),
            nat,
            zero,
        }
    }

    fn list_spec(parameter: TypeParameter) -> InductiveSpec {
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
        )
    }

    #[test]
    fn parameterized_list_registers_typed_constructor_schemes() {
        let mut fixture = fixture();
        let parameter = TypeParameter::any(0);
        let list_id = fixture
            .inductives
            .declare(
                &mut fixture.types,
                &mut fixture.constants,
                list_spec(parameter),
            )
            .expect("List");
        let list_nat = CoreType::constructor(list_id, vec![fixture.nat.clone()]);
        let nil = fixture.constants.resolve("nil").expect("nil");
        let cons = fixture.constants.resolve("cons").expect("cons");
        let nil_nat = CoreTerm::instantiate_constant(nil, vec![fixture.nat.clone()]);
        let one_element = CoreTerm::apply(
            CoreTerm::apply(
                CoreTerm::instantiate_constant(cons, vec![fixture.nat.clone()]),
                CoreTerm::Constant(fixture.zero),
            ),
            nil_nat,
        );

        assert_eq!(
            infer_type(
                &fixture.types,
                &fixture.constants,
                &TermContext::new(),
                &one_element,
            ),
            Ok(list_nat.clone())
        );
        assert_eq!(
            fixture.types.first_order_status(&list_nat),
            Ok(FirstOrderStatus::FirstOrder)
        );
        let declaration = fixture
            .inductives
            .declaration(list_id)
            .expect("List metadata");
        assert!(declaration.preserves_first_order);
        assert_eq!(declaration.constructors[1].recursive_fields, vec![1]);
    }

    #[test]
    fn constructor_metadata_instantiates_fields_and_result() {
        let mut fixture = fixture();
        let parameter = TypeParameter::any(0);
        let list_id = fixture
            .inductives
            .declare(
                &mut fixture.types,
                &mut fixture.constants,
                list_spec(parameter),
            )
            .expect("List");
        let cons = fixture.constants.resolve("cons").expect("cons");
        let instantiated = fixture
            .inductives
            .instantiate_constructor(&fixture.types, cons, std::slice::from_ref(&fixture.nat))
            .expect("cons Nat metadata");
        let list_nat = CoreType::constructor(list_id, vec![fixture.nat.clone()]);
        assert_eq!(
            instantiated.field_types,
            vec![fixture.nat, list_nat.clone()]
        );
        assert_eq!(instantiated.result_type, list_nat);
        assert_eq!(instantiated.recursive_fields, vec![1]);
    }

    #[test]
    fn negative_recursive_occurrence_is_rejected_atomically() {
        let mut fixture = fixture();
        let bad = InductiveSpec::new(
            "Bad",
            Vec::new(),
            vec![InductiveConstructorSpec::new(
                "make_bad",
                vec![InductiveFieldType::arrow(
                    InductiveFieldType::Recursive,
                    InductiveFieldType::existing(fixture.nat.clone()),
                )],
            )],
        );
        let error = fixture
            .inductives
            .declare(&mut fixture.types, &mut fixture.constants, bad)
            .expect_err("negative datatype must fail");
        assert!(error.message.contains("occurs negatively"));
        assert_eq!(fixture.types.resolve("Bad"), None);
        assert_eq!(fixture.constants.resolve("make_bad"), None);
    }

    #[test]
    fn positive_but_nested_recursion_is_deferred_and_rejected_atomically() {
        let mut fixture = fixture();
        let nested = InductiveSpec::new(
            "Nested",
            Vec::new(),
            vec![InductiveConstructorSpec::new(
                "make_nested",
                vec![InductiveFieldType::product(
                    InductiveFieldType::Recursive,
                    InductiveFieldType::existing(fixture.nat.clone()),
                )],
            )],
        );
        let error = fixture
            .inductives
            .declare(&mut fixture.types, &mut fixture.constants, nested)
            .expect_err("nested recursion is not in the first spike");
        assert!(error.message.contains("nested recursive occurrences"));
        assert_eq!(fixture.types.resolve("Nested"), None);
        assert_eq!(fixture.constants.resolve("make_nested"), None);
    }

    #[test]
    fn duplicate_constructor_names_leave_signatures_unchanged() {
        let mut fixture = fixture();
        let duplicate = InductiveSpec::new(
            "Bit",
            Vec::new(),
            vec![
                InductiveConstructorSpec::new("bit", Vec::new()),
                InductiveConstructorSpec::new("bit", Vec::new()),
            ],
        );
        let error = fixture
            .inductives
            .declare(&mut fixture.types, &mut fixture.constants, duplicate)
            .expect_err("duplicate constructor must fail");
        assert!(error.message.contains("repeats constructor name"));
        assert_eq!(fixture.types.resolve("Bit"), None);
        assert_eq!(fixture.constants.resolve("bit"), None);
    }

    #[test]
    fn prop_and_function_fields_prevent_first_order_classification() {
        let mut fixture = fixture();
        let evidence_id = fixture
            .inductives
            .declare(
                &mut fixture.types,
                &mut fixture.constants,
                InductiveSpec::new(
                    "Evidence",
                    Vec::new(),
                    vec![InductiveConstructorSpec::new(
                        "evidence",
                        vec![InductiveFieldType::existing(CoreType::Prop)],
                    )],
                ),
            )
            .expect("Evidence is sound but higher-order data");
        assert_eq!(
            fixture
                .types
                .first_order_status(&CoreType::constructor(evidence_id, Vec::new())),
            Ok(FirstOrderStatus::HigherOrder)
        );

        let function_id = fixture
            .inductives
            .declare(
                &mut fixture.types,
                &mut fixture.constants,
                InductiveSpec::new(
                    "FunctionBox",
                    Vec::new(),
                    vec![InductiveConstructorSpec::new(
                        "function_box",
                        vec![InductiveFieldType::existing(CoreType::arrow(
                            fixture.nat.clone(),
                            fixture.nat.clone(),
                        ))],
                    )],
                ),
            )
            .expect("function field is sound");
        assert_eq!(
            fixture
                .types
                .first_order_status(&CoreType::constructor(function_id, Vec::new())),
            Ok(FirstOrderStatus::HigherOrder)
        );
    }

    #[test]
    fn invalid_existing_field_type_does_not_reserve_names() {
        let mut fixture = fixture();
        let invalid = InductiveSpec::new(
            "Broken",
            Vec::new(),
            vec![InductiveConstructorSpec::new(
                "broken",
                vec![InductiveFieldType::existing(CoreType::constructor(
                    TypeConstructorId(999),
                    Vec::new(),
                ))],
            )],
        );
        let error = fixture
            .inductives
            .declare(&mut fixture.types, &mut fixture.constants, invalid)
            .expect_err("unknown field type must fail");
        assert!(error.message.contains("unknown type constructor"));
        assert_eq!(fixture.types.resolve("Broken"), None);
        assert_eq!(fixture.constants.resolve("broken"), None);
    }
}
