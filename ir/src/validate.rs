// Copyright (C) 2025 Marceline Cramer
// SPDX-License-Identifier: AGPL-3.0-or-later
//
// Saturn V is free software: you can redistribute it and/or modify it under
// the terms of the GNU Affero General Public License as published by the Free
// Software Foundation, either version 3 of the License, or (at your option) any
// later version.
//
// Saturn V is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
// FOR A PARTICULAR PURPOSE. See the GNU Affero General Public License for
// more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with Saturn V. If not, see <https://www.gnu.org/licenses/>.

use std::fmt::Display;

use super::*;

impl<R: Clone + Eq + Hash> Program<R> {
    /// Validates this program.
    pub fn validate(&self) -> Result<(), R> {
        // build a table of all relation types
        let mut relation_tys = HashMap::new();
        for (new, r) in self.relations.values().enumerate() {
            if let Some((old, _ty)) = relation_tys.insert(r.store.clone(), (new, r.ty.clone())) {
                return Err(ErrorKind::DuplicateRelationUserdata {
                    relation: r.store.clone(),
                    old,
                    new,
                }
                .into());
            }
        }

        // strip out indices from relations now that we've validated duplicates
        let relation_tys: HashMap<_, _> = relation_tys
            .into_iter()
            .map(|(r, (_idx, ty))| (r, ty))
            .collect();

        // validate all of the relations
        for r in self.relations.values() {
            r.validate(&relation_tys)
                .with_context(ErrorContext::Relation(r.store.clone()))?;
        }

        // validate all of the constraints
        for (idx, c) in self.constraints.iter().enumerate() {
            c.validate(&relation_tys)
                .with_context(ErrorContext::Constraint(idx))?;
        }

        // create a map of each relation to a decision relation dependency, if any
        let decision_dependencies: HashMap<&R, Option<&R>> = self
            .indirect_dependencies()
            .into_iter()
            .map(|(dependent, dependencies)| {
                let decision = dependencies
                    .into_iter()
                    .find(|dep| self.relations[*dep].kind == RelationKind::Decision);

                (dependent, decision)
            })
            .collect();

        // validate of each relation's kind
        for (relation, decision) in decision_dependencies {
            match (self.relations[relation].kind, decision) {
                // basic relations must not have indirect decision dependencies
                (RelationKind::Basic, Some(decision)) => {
                    return Err(ErrorKind::BasicRelationDependsOnDecision {
                        basic: relation.clone(),
                        decision: decision.clone(),
                    }
                    .into())
                }
                // conditional relations must be dependent on decisions
                (RelationKind::Conditional, None) => {
                    return Err(ErrorKind::ConditionalRelationHasNoDecisions {
                        conditional: relation.clone(),
                    }
                    .into())
                }
                // all other relation kinds are valid!
                _ => {}
            }
        }

        // all done!
        Ok(())
    }

    /// Create a map of each relation's indirect dependencies.
    pub fn indirect_dependencies(&self) -> HashMap<&R, HashSet<&R>> {
        // initialize an empty indirect dep map
        let mut indirect: HashMap<_, HashSet<_>> = HashMap::new();

        // create the initial stack of new deps out of direct deps
        let mut stack: Vec<_> = self
            .relations
            .iter()
            .flat_map(|(key, relation)| {
                relation
                    .direct_dependencies()
                    .into_iter()
                    .map(move |dep| (key, dep))
            })
            .collect();

        // until the stack is empty, add dependencies
        while let Some((dependent, dependency)) = stack.pop() {
            // if the dependency is already in the map, skip adding indirect deps
            if !indirect.entry(dependent).or_default().insert(dependency) {
                continue;
            }

            // otherwise, add the indirect dependencies to the stack
            for indirect_dep in self.relations[dependency].direct_dependencies() {
                stack.push((dependent, indirect_dep));
            }
        }

        // we've reached a fixed point; return the complete dependency map
        indirect
    }
}

impl<R: Clone + Hash + Eq> Constraint<R> {
    /// Validates this constraint.
    pub fn validate(&self, relations: &HashMap<R, Vec<Type>>) -> Result<(), R> {
        // first, validate the rule body
        let assigned = self.body.validate(relations)?;

        // next, find which variables are needed and track the head type
        let mut needed = HashSet::new();
        for idx in self.head.iter().copied() {
            // check that the variable exists
            self.body
                .vars
                .get(idx as usize)
                .ok_or(ErrorKind::InvalidVariableIndex(idx))?;

            // insert the variable
            needed.insert(idx);
        }

        // if there are any unassigned but needed variables, return an error
        let unassigned: HashSet<_> = needed.difference(&assigned).copied().collect();
        if !unassigned.is_empty() {
            return Err(ErrorKind::UnassignedVariables(unassigned).into());
        }

        // otherwise, this constraint is valid
        Ok(())
    }
}

impl<R: Clone + Eq + Hash> Relation<R> {
    /// Validates this relation.
    pub fn validate(&self, relations: &HashMap<R, Vec<Type>>) -> Result<(), R> {
        // check that each fact matches this relation's type
        for fact in self.facts.iter() {
            let ty: Vec<_> = fact.iter().map(Value::ty).collect();

            if ty != self.ty {
                return Err(ErrorKind::ExpectedTupleType {
                    expected: self.ty.clone(),
                    got: ty,
                }
                .into());
            }
        }

        // validate each rule
        for (idx, rule) in self.rules.iter().enumerate() {
            // validate the rule itself
            let ty = rule
                .validate(relations)
                .with_context(ErrorContext::Rule(idx))?;

            // check the type of the head against this relation
            if ty != self.ty {
                return Err(ErrorKind::ExpectedTupleType {
                    expected: self.ty.clone(),
                    got: ty,
                })
                .with_context(ErrorContext::Rule(idx));
            }
        }

        // this relation is valid!
        Ok(())
    }

    /// Get the set of direct dependencies this relation possesses.
    pub fn direct_dependencies(&self) -> HashSet<&R> {
        self.rules
            .iter()
            .flat_map(|rule| rule.body.loaded.iter())
            .collect()
    }
}

impl<R: Clone + Eq + Hash> Rule<R> {
    /// Validates this rule and returns the type of the head.
    pub fn validate(&self, relations: &HashMap<R, Vec<Type>>) -> Result<Vec<Type>, R> {
        // first, validate the rule body
        let assigned = self.body.validate(relations)?;

        // next, find which variables are needed and track the head type
        let mut ty = Vec::new();
        let mut needed = HashSet::new();
        for (idx, term) in self.head.iter().enumerate() {
            match term {
                // simply push value types to the running rule type
                QueryTerm::Value(val) => {
                    ty.push(val.ty());
                    continue;
                }
                // check that the variable exists, push its type, and insert it
                QueryTerm::Variable(var) => {
                    let var = *var;

                    let var_ty = self
                        .body
                        .vars
                        .get(var as usize)
                        .ok_or(ErrorKind::InvalidVariableIndex(var))
                        .with_context(ErrorContext::QueryTerm(idx))?;

                    ty.push(*var_ty);
                    needed.insert(var);
                }
            }
        }

        // if there are any unassigned but needed variables, return an error
        let unassigned: HashSet<_> = needed.difference(&assigned).copied().collect();
        if !unassigned.is_empty() {
            return Err(ErrorKind::UnassignedVariables(unassigned).into());
        }

        // otherwise, this rule is valid
        Ok(ty)
    }
}

impl<R: Clone + Eq + Hash> RuleBody<R> {
    /// Validates this rule body, returning the set of assigned variables.
    pub fn validate(&self, relations: &HashMap<R, Vec<Type>>) -> Result<HashSet<u32>, R> {
        // first, confirm that all necessary variables are assigned
        let relations = validate_load_relations(relations, &self.loaded)?;
        let assigned = self.instructions.validate(&relations, &self.vars)?;

        // if there are any unused relations, return an error
        let used = self.instructions.relation_deps();
        let declared: HashSet<u32> = (0..(self.loaded.len() as u32)).collect();
        let unused: HashSet<_> = used.difference(&declared).copied().collect();
        if !unused.is_empty() {
            return Err(ErrorKind::UnusedRelations(unused).into());
        }

        // otherwise, this rule body is valid
        Ok(assigned)
    }
}

impl Instruction {
    /// Validates this expression and returns its assigned variables.
    pub fn validate<R>(
        &self,
        relations: &[Vec<Type>],
        variables: &[Type],
    ) -> Result<HashSet<u32>, R> {
        let vars = self
            .validate_inner(relations, variables)
            .with_context(ErrorContext::Instruction(self.into()))?;

        Ok(vars)
    }

    /// ACTUALLY validates, but doesn't wrap the error in the instruction kind context.
    fn validate_inner<R>(
        &self,
        relations: &[Vec<Type>],
        variables: &[Type],
    ) -> Result<HashSet<u32>, R> {
        use Instruction::*;
        match self {
            Noop => Err(ErrorKind::Noop.into()),
            Sink { rest, .. } => {
                // TODO: just ignore sinks? where should unassigned variables be handled?
                rest.validate(relations, variables)
            }
            Filter { test, rest } => {
                // validate the dependencies
                let vars = rest.validate(relations, variables)?;
                let ty = test.validate(relations, variables)?;

                // check for unassigned variables used by the test
                let used = test.variable_deps();
                let unassigned: HashSet<_> = used.difference(&vars).copied().collect();
                if !unassigned.is_empty() {
                    return Err(ErrorKind::UnassignedVariables(unassigned).into());
                }

                // for a filter expression, we always require a Boolean
                if ty != Type::Boolean {
                    return Err(ErrorKind::ExpectedType {
                        expected: Type::Boolean,
                        got: ty,
                    }
                    .into());
                }

                Ok(vars)
            }
            FromQuery { relation, terms } => validate_query(relations, variables, *relation, terms),
            Let { var, expr, rest } => {
                // typecast variable
                let var = *var;

                // validate the dependencies
                let mut vars = rest.validate(relations, variables)?;
                let got_ty = expr.validate(relations, variables)?;

                // assert that the variable is not assigned twice
                if vars.contains(&var) {
                    return Err(ErrorKind::VariableAssignedTwice(var).into());
                }

                // retrieve the type of the variable (if it exists)
                let expected_ty = variables
                    .get(var as usize)
                    .cloned()
                    .ok_or(ErrorKind::InvalidVariableIndex(var))?;

                // check for unassigned variables used by the expression
                let used = expr.variable_deps();
                let unassigned: HashSet<_> = used.difference(&vars).copied().collect();
                if !unassigned.is_empty() {
                    return Err(ErrorKind::UnassignedVariables(unassigned).into());
                }

                // insert the new variable into the assigned set
                vars.insert(var);

                // confirm that the type of the expression matches the variable
                if got_ty != expected_ty {
                    return Err(ErrorKind::ExpectedType {
                        expected: expected_ty,
                        got: got_ty,
                    }
                    .into());
                }

                Ok(vars)
            }
            Merge { lhs, rhs } => {
                // validate each branch first
                let lhs = lhs
                    .validate(relations, variables)
                    .with_context(ErrorContext::Left)?;

                let rhs = rhs
                    .validate(relations, variables)
                    .with_context(ErrorContext::Right)?;

                // test for equality of the two sides
                if lhs == rhs {
                    Ok(lhs)
                } else {
                    // otherwise report an error
                    let lhs_only: HashSet<_> = lhs.difference(&rhs).copied().collect();
                    let rhs_only: HashSet<_> = rhs.difference(&lhs).copied().collect();
                    Err(ErrorKind::MergeVariableMismatch { lhs_only, rhs_only }.into())
                }
            }
            Join { lhs, rhs } => {
                // just take the union of either branch
                let mut lhs = lhs
                    .validate(relations, variables)
                    .with_context(ErrorContext::Left)?;

                let rhs = rhs
                    .validate(relations, variables)
                    .with_context(ErrorContext::Right)?;

                lhs.extend(rhs);
                Ok(lhs)
            }
        }
    }

    /// Retrieves the set of relations used by this instruction.
    pub fn relation_deps(&self) -> HashSet<u32> {
        use Instruction::*;
        match self {
            Noop => HashSet::new(),
            Sink { rest, .. } => rest.relation_deps(),
            FromQuery { relation, .. } => HashSet::from_iter([*relation]),
            Filter { test, rest } => {
                let mut relations = rest.relation_deps();
                relations.extend(test.relation_deps());
                relations
            }
            Let { expr, rest, .. } => {
                let mut relations = rest.relation_deps();
                relations.extend(expr.relation_deps());
                relations
            }
            Merge { lhs, rhs } | Join { lhs, rhs } => {
                let mut relations = lhs.relation_deps();
                relations.extend(rhs.relation_deps());
                relations
            }
        }
    }
}

impl Expr {
    /// Validates this expression and returns its type.
    pub fn validate<R>(&self, relations: &[Vec<Type>], variables: &[Type]) -> Result<Type, R> {
        use Expr::*;
        match self {
            Variable(idx) => variables
                .get(*idx as usize)
                .cloned()
                .ok_or(ErrorKind::InvalidVariableIndex(*idx).into()),
            Value(val) => Ok(val.ty()),
            Load { relation, query } => {
                validate_query(relations, variables, *relation, query)?;
                Ok(Type::Boolean)
            }
            UnaryOp { op, term } => {
                let term = term
                    .validate(relations, variables)
                    .with_context(ErrorContext::UnaryOp(*op))?;

                use Type::*;
                use UnaryOpKind::*;
                match (op, term) {
                    (Not, Boolean) => Ok(Boolean),
                    (Negate, Integer) => Ok(Integer),
                    (Negate, Real) => Ok(Real),
                    (op, term) => Err(ErrorKind::InvalidUnaryOp { op: *op, term }.into()),
                }
            }
            BinaryOp { op, lhs, rhs } => {
                let lhs = lhs
                    .validate(relations, variables)
                    .with_context(ErrorContext::Left)
                    .with_context(ErrorContext::BinaryOp(*op))?;

                let rhs = rhs
                    .validate(relations, variables)
                    .with_context(ErrorContext::Right)
                    .with_context(ErrorContext::BinaryOp(*op))?;

                use Type::*;
                match (op.category(), lhs, rhs) {
                    (BinaryOpCategory::Arithmetic, Integer, Integer) => Ok(Integer),
                    (BinaryOpCategory::Arithmetic, Real, Real) => Ok(Real),
                    (BinaryOpCategory::String, String, String) => Ok(String),
                    (BinaryOpCategory::Logical, Boolean, Boolean) => Ok(Boolean),
                    (BinaryOpCategory::Comparison, lhs, rhs) if lhs == rhs => Ok(Boolean),
                    (_, lhs, rhs) => Err(ErrorKind::InvalidBinaryOp { op: *op, lhs, rhs }.into()),
                }
            }
        }
    }

    /// Retrieves the set of variables accessed by this expression.
    pub fn variable_deps(&self) -> HashSet<u32> {
        use Expr::*;
        match self {
            Variable(idx) => HashSet::from_iter([*idx]),
            Value(_) => HashSet::new(),
            Load { query, .. } => query
                .iter()
                .flat_map(|term| match term {
                    QueryTerm::Value(_) => None,
                    QueryTerm::Variable(idx) => Some(*idx),
                })
                .collect(),
            UnaryOp { term, .. } => term.variable_deps(),
            BinaryOp { lhs, rhs, .. } => {
                let mut vars = lhs.variable_deps();
                vars.extend(rhs.variable_deps());
                vars
            }
        }
    }

    /// Retrieves the set of relations accessed by this expression.
    pub fn relation_deps(&self) -> HashSet<u32> {
        use Expr::*;
        match self {
            Load { relation, .. } => HashSet::from_iter([*relation]),
            UnaryOp { term, .. } => term.relation_deps(),
            BinaryOp { lhs, rhs, .. } => {
                let mut vars = lhs.relation_deps();
                vars.extend(rhs.relation_deps());
                vars
            }
            _ => HashSet::new(),
        }
    }
}

/// Retrieves the types of loaded relations by userdata.
pub fn validate_load_relations<R: Clone + Eq + Hash>(
    types: &HashMap<R, Vec<Type>>,
    relations: &[R],
) -> Result<Vec<Vec<Type>>, R> {
    let mut out = Vec::new();
    for (idx, relation) in relations.iter().enumerate() {
        if let Some((old, _decision)) = relations[0..idx]
            .iter()
            .enumerate()
            .find(|(_idx, old)| *old == relation)
        {
            return Err(ErrorKind::DuplicateRelationUserdata {
                relation: relation.clone(),
                old,
                new: idx,
            }
            .into());
        }

        out.push(
            types
                .get(relation)
                .ok_or(ErrorKind::RelationNotFound(relation.clone()))?
                .clone(),
        );
    }

    Ok(out)
}

/// Validate a query and return its used variables.
pub fn validate_query<R>(
    relations: &[Vec<Type>],
    variables: &[Type],
    relation: u32,
    terms: &[QueryTerm],
) -> Result<HashSet<u32>, R> {
    // retrieve the type of the relation
    let relation_ty = relations
        .get(relation as usize)
        .ok_or(ErrorKind::InvalidRelationIndex(relation))?
        .iter()
        .copied();

    // if the lengths of the relation and terms are different, the type cannot match
    if relation_ty.len() != terms.len() {
        return Err(ErrorKind::QuerySizeMismatch {
            relation,
            expected: relation_ty.len(),
            got: terms.len(),
        }
        .into());
    }

    // collect list of assigned variables
    let mut vars = HashSet::new();
    for ((idx, term), expected) in terms.iter().enumerate().zip(relation_ty) {
        // get the type of the term
        let got = match term {
            QueryTerm::Value(val) => val.ty(),
            QueryTerm::Variable(var) => {
                // ensure that the variable is only used once per query
                if !vars.insert(*var) {
                    return Err(ErrorKind::DuplicateQueryVariable(*var))
                        .with_context(ErrorContext::QueryTerm(idx));
                }

                // retrieve the type of the variable
                *variables
                    .get(*var as usize)
                    .ok_or(ErrorKind::InvalidVariableIndex(*var))
                    .with_context(ErrorContext::QueryTerm(idx))?
            }
        };

        // ensure that types match
        if expected != got {
            return Err(ErrorKind::ExpectedType { expected, got })
                .with_context(ErrorContext::QueryTerm(idx))?;
        }
    }

    Ok(vars)
}

pub type Result<T, R> = std::result::Result<T, Error<R>>;

pub trait WithContext<R> {
    type Output;
    fn with_context(self, ctx: ErrorContext<R>) -> Self::Output;
}

impl<T, R> WithContext<R> for std::result::Result<T, ErrorKind<R>> {
    type Output = Result<T, R>;

    fn with_context(self, ctx: ErrorContext<R>) -> Self::Output {
        self.map_err(|kind| Error {
            kind: Box::new(kind),
            context: vec![ctx],
        })
    }
}

impl<T, R> WithContext<R> for Result<T, R> {
    type Output = Self;

    fn with_context(mut self, ctx: ErrorContext<R>) -> Self {
        if let Err(error) = self.as_mut() {
            error.context.push(ctx);
        }

        self
    }
}

#[derive(Clone, Debug)]
pub struct Error<R> {
    pub context: Vec<ErrorContext<R>>,
    pub kind: Box<ErrorKind<R>>,
}

impl<R> From<ErrorKind<R>> for Error<R> {
    fn from(kind: ErrorKind<R>) -> Self {
        Self {
            context: vec![],
            kind: Box::new(kind),
        }
    }
}

impl<R: Display> Display for Error<R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "validation error")?;

        for ctx in self.context.iter().rev() {
            writeln!(f, "  {ctx}")?;
        }

        writeln!(f, "  {}", self.kind)
    }
}

#[derive(Clone, Debug, thiserror::Error)]
pub enum ErrorContext<R> {
    #[error("in {0:?} instruction")]
    Instruction(InstructionKind),

    #[error("in relation {0}")]
    Relation(R),

    #[error("in {0:?} binary operation")]
    BinaryOp(BinaryOpKind),

    #[error("in {0:?} unary operation")]
    UnaryOp(UnaryOpKind),

    #[error("in constraint #{0}")]
    Constraint(usize),

    #[error("in rule #{0}")]
    Rule(usize),

    #[error("in query term #{0}")]
    QueryTerm(usize),

    #[error("in left branch")]
    Left,

    #[error("in right branch")]
    Right,
}

#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ErrorKind<R> {
    #[error("relation index #{0} is invalid")]
    InvalidRelationIndex(u32),

    #[error("variable index #{0} is invalid")]
    InvalidVariableIndex(u32),

    #[error("duplicate relation in #{old} and #{new}: {relation}")]
    DuplicateRelationUserdata { relation: R, old: usize, new: usize },

    #[error("the basic relation {basic} depends on decision relation {decision}")]
    BasicRelationDependsOnDecision { basic: R, decision: R },

    #[error("conditional relation {conditional} has no dependencies on decisions")]
    ConditionalRelationHasNoDecisions { conditional: R },

    #[error("could not find relation by userdata: {0}")]
    RelationNotFound(R),

    #[error("invalid binary operation: {lhs:?} {op:?} {rhs:?}")]
    InvalidBinaryOp {
        op: BinaryOpKind,
        lhs: Type,
        rhs: Type,
    },

    #[error("invalid unary operation: {op:?} {term:?}")]
    InvalidUnaryOp { op: UnaryOpKind, term: Type },

    #[error("relation query has length {got} but relation #{relation} is length {expected}")]
    QuerySizeMismatch {
        relation: u32,
        expected: usize,
        got: usize,
    },

    #[error("expected {expected:?}, got {got:?}")]
    ExpectedType { expected: Type, got: Type },

    #[error("expected tuple type {expected:?}, got {got:?}")]
    ExpectedTupleType { expected: Vec<Type>, got: Vec<Type> },

    #[error("variable #{0} is assigned twice")]
    VariableAssignedTwice(u32),

    #[error("unassigned variables: {0:?}")]
    UnassignedVariables(HashSet<u32>),

    #[error("unused relations: {0:?}")]
    UnusedRelations(HashSet<u32>),

    #[error("merge branches have mismatching variables. lhs: {lhs_only:?} rhs: {rhs_only:?}")]
    MergeVariableMismatch {
        lhs_only: HashSet<u32>,
        rhs_only: HashSet<u32>,
    },

    #[error("variable #{0} is used twice in the same query")]
    DuplicateQueryVariable(u32),

    #[error("no-ops are invalid")]
    Noop,
}
