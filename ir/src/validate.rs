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

use super::*;

impl<R> Program<R> {
    /// Validates this program.
    pub fn validate(&self) -> Result<()> {
        // validate all of the relations
        for r in self.relations.values() {
            // TODO: add relation context
            r.validate()?;
        }

        // validate all of the constraints
        for (idx, c) in self.constraints.iter().enumerate() {
            c.validate().with_context(ErrorContext::Constraint(idx))?;
        }

        // all done!
        Ok(())
    }
}

impl<R> Constraint<R> {
    /// Validates this constraint.
    pub fn validate(&self) -> Result<()> {
        // first, confirm that all necessary variables are assigned
        let assigned = self.instructions.validate(&self.loaded, &self.vars)?;

        // next, find which variables are needed and track the head type
        let mut needed = HashSet::new();
        for idx in self.head.iter().copied() {
            // check that the variable exists
            self.vars
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

impl<R> Relation<R> {
    /// Validates this relation.
    pub fn validate(&self) -> Result<()> {
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
            let ty = rule.validate().with_context(ErrorContext::Rule(idx))?;

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
}

impl<R> Rule<R> {
    /// Validates this rule and returns the type of the head.
    pub fn validate(&self) -> Result<Vec<Type>> {
        // first, confirm that all necessary variables are assigned
        let assigned = self.instructions.validate(&self.loaded, &self.vars)?;

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

impl Instruction {
    /// Validates this expression and returns its assigned variables.
    pub fn validate<T>(&self, relations: &[T], variables: &[Type]) -> Result<HashSet<u32>> {
        self.validate_inner(relations, variables)
            .with_context(ErrorContext::Instruction(self.into()))
    }

    /// ACTUALLY validates, but doesn't wrap the error in the instruction kind context.
    fn validate_inner<T>(&self, relations: &[T], variables: &[Type]) -> Result<HashSet<u32>> {
        use Instruction::*;
        match self {
            Noop => Ok(HashSet::new()),
            Sink(_vars, rest) => {
                // TODO: just ignore sinks? where should unassigned variables be handled?
                rest.validate(relations, variables)
            }
            Filter(expr, rest) => {
                // validate the dependencies
                let vars = rest.validate(relations, variables)?;
                let ty = expr.validate(relations, variables)?;

                // check for unassigned variables used by the expression
                let used = expr.variable_deps();
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
            FromQuery(relation, terms) => {
                // assert that the relation index is valid
                if *relation >= relations.len() as u32 {
                    return Err(ErrorKind::InvalidRelationIndex(*relation).into());
                }

                // collect list of assigned variables
                let mut vars = HashSet::new();
                for (idx, term) in terms.iter().enumerate() {
                    // ignore value terms; we only care about variables
                    let QueryTerm::Variable(var) = term else {
                        continue;
                    };

                    // check that the variable exists
                    variables
                        .get(*var as usize)
                        .ok_or(ErrorKind::InvalidVariableIndex(*var))
                        .with_context(ErrorContext::QueryTerm(idx))?;

                    // ensure that the variable is only used once per query
                    if !vars.insert(*var) {
                        return Err(ErrorKind::DuplicateQueryVariable(*var))
                            .with_context(ErrorContext::QueryTerm(idx));
                    }
                }

                Ok(vars)
            }
            Let(var, expr, rest) => {
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
            Merge(lhs, rhs) => {
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
            Join(lhs, rhs) => {
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
}

impl Expr {
    /// Validates this expression and returns its type.
    pub fn validate<T>(&self, relations: &[T], variables: &[Type]) -> Result<Type> {
        use Expr::*;
        match self {
            Variable(idx) => variables
                .get(*idx as usize)
                .cloned()
                .ok_or(ErrorKind::InvalidVariableIndex(*idx).into()),
            Value(val) => Ok(val.ty()),
            Load { relation, query } => {
                if *relation >= relations.len() as u32 {
                    return Err(ErrorKind::InvalidRelationIndex(*relation).into());
                }

                for (idx, term) in query.iter().enumerate() {
                    match term {
                        QueryTerm::Variable(var) => {
                            if *var >= variables.len() as u32 {
                                return Err(ErrorKind::InvalidVariableIndex(*var))
                                    .with_context(ErrorContext::QueryTerm(idx));
                            }
                        }
                        QueryTerm::Value(_) => {}
                    }
                }

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
}

pub type Result<T> = std::result::Result<T, Error>;

pub trait WithContext {
    type Output;
    fn with_context(self, ctx: ErrorContext) -> Self::Output;
}

impl<T> WithContext for std::result::Result<T, ErrorKind> {
    type Output = Result<T>;

    fn with_context(self, ctx: ErrorContext) -> Self::Output {
        self.map_err(|kind| Error {
            kind: Box::new(kind),
            context: vec![ctx],
        })
    }
}

impl<T> WithContext for Result<T> {
    type Output = Self;

    fn with_context(mut self, ctx: ErrorContext) -> Self {
        if let Err(error) = self.as_mut() {
            error.context.push(ctx);
        }

        self
    }
}

#[derive(Clone, Debug)]
pub struct Error {
    pub context: Vec<ErrorContext>,
    pub kind: Box<ErrorKind>,
}

impl From<ErrorKind> for Error {
    fn from(kind: ErrorKind) -> Self {
        Self {
            context: vec![],
            kind: Box::new(kind),
        }
    }
}

#[derive(Clone, Debug)]
pub enum ErrorContext {
    Instruction(InstructionKind),
    BinaryOp(BinaryOpKind),
    UnaryOp(UnaryOpKind),
    Constraint(usize),
    Rule(usize),
    QueryTerm(usize),
    Left,
    Right,
}

#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ErrorKind {
    #[error("relation index #{0} is invalid")]
    InvalidRelationIndex(u32),

    #[error("variable index #{0} is invalid")]
    InvalidVariableIndex(u32),

    #[error("invalid binary operation: {lhs:?} {op:?} {rhs:?}")]
    InvalidBinaryOp {
        op: BinaryOpKind,
        lhs: Type,
        rhs: Type,
    },

    #[error("invalid unary operation: {op:?} {term:?}")]
    InvalidUnaryOp { op: UnaryOpKind, term: Type },

    #[error("expected {expected:?}, got {got:?}")]
    ExpectedType { expected: Type, got: Type },

    #[error("expected tuple type {expected:?}, got {got:?}")]
    ExpectedTupleType { expected: Vec<Type>, got: Vec<Type> },

    #[error("variable #{0} is assigned twice")]
    VariableAssignedTwice(u32),

    #[error("unassigned variables: {0:?}")]
    UnassignedVariables(HashSet<u32>),

    #[error("merge branches have mismatching variables. lhs: {lhs_only:?} rhs: {rhs_only:?}")]
    MergeVariableMismatch {
        lhs_only: HashSet<u32>,
        rhs_only: HashSet<u32>,
    },

    #[error("variable #{0} is used twice in the same query")]
    DuplicateQueryVariable(u32),
}
