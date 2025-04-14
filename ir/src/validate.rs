use super::*;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    InvalidRelationIndex(usize),
    InvalidVariableIndex(usize),
    InvalidBinaryOp {
        op: BinaryOpKind,
        lhs: Type,
        rhs: Type,
    },
    InvalidUnaryOp {
        op: UnaryOpKind,
        term: Type,
    },
    ExpectedType {
        expected: Type,
        got: Type,
    },
    ExpectedTupleType {
        expected: Vec<Type>,
        got: Vec<Type>,
    },
    VariableAssignedTwice(usize),
    UnassignedVariables(HashSet<usize>),
    MergeVariableMismatch {
        lhs_only: HashSet<usize>,
        rhs_only: HashSet<usize>,
    },
    DuplicateQueryVariable(usize),
}

impl<R> Program<R> {
    /// Validates this program.
    pub fn validate(&self) -> Result<()> {
        // validate all of the relations
        for r in self.relations.values() {
            r.validate()?;
        }

        // validate all of the constraints
        for c in self.constraints.iter() {
            c.validate()?;
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
            self.vars.get(idx).ok_or(Error::InvalidVariableIndex(idx))?;

            // insert the variable
            needed.insert(idx);
        }

        // if there are any unassigned but needed variables, return an error
        let unassigned: HashSet<_> = needed.difference(&assigned).copied().collect();
        if !unassigned.is_empty() {
            return Err(Error::UnassignedVariables(unassigned));
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
                return Err(Error::ExpectedTupleType {
                    expected: self.ty.clone(),
                    got: ty,
                });
            }
        }

        // validate each rule
        for rule in self.rules.iter() {
            // validate the rule itself
            let ty = rule.validate()?;

            // check the type of the head against this relation
            if ty != self.ty {
                return Err(Error::ExpectedTupleType {
                    expected: self.ty.clone(),
                    got: ty,
                });
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
        for term in self.head.iter() {
            // process this term
            let idx = match term {
                // simply push value types to the running rule type
                QueryTerm::Value(val) => {
                    ty.push(val.ty());
                    continue;
                }
                // process variables further
                QueryTerm::Variable(idx) => *idx,
            };

            // check that the variable exists
            self.vars.get(idx).ok_or(Error::InvalidVariableIndex(idx))?;

            // insert the variable
            needed.insert(idx);
        }

        // if there are any unassigned but needed variables, return an error
        let unassigned: HashSet<_> = needed.difference(&assigned).copied().collect();
        if !unassigned.is_empty() {
            return Err(Error::UnassignedVariables(unassigned));
        }

        // otherwise, this rule is valid
        Ok(ty)
    }
}

impl Instruction {
    /// Validates this expression and returns its assigned variables.
    pub fn validate<T>(&self, relations: &[T], variables: &[Type]) -> Result<HashSet<usize>> {
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
                let unassigned: HashSet<usize> = used.difference(&vars).copied().collect();
                if !unassigned.is_empty() {
                    return Err(Error::UnassignedVariables(unassigned));
                }

                // for a filter expression, we always require a Boolean
                if ty != Type::Boolean {
                    return Err(Error::ExpectedType {
                        expected: Type::Boolean,
                        got: ty,
                    });
                }

                Ok(vars)
            }
            FromQuery(_relation, terms) => {
                let mut vars = HashSet::new();

                for term in terms.iter() {
                    // ignore value terms; we only care about variables
                    let QueryTerm::Variable(idx) = term else {
                        continue;
                    };

                    // check that the variable exists
                    variables
                        .get(*idx)
                        .ok_or(Error::InvalidVariableIndex(*idx))?;

                    // ensure that the variable is only used once per query
                    if vars.insert(*idx) {
                        return Err(Error::DuplicateQueryVariable(*idx));
                    }
                }

                Ok(vars)
            }
            Let(var, expr, rest) => {
                // validate the dependencies
                let vars = rest.validate(relations, variables)?;
                let got_ty = expr.validate(relations, variables)?;

                // retrieve the type of the variable (if it exists)
                let expected_ty = variables
                    .get(*var as usize)
                    .cloned()
                    .ok_or(Error::InvalidVariableIndex(*var as usize))?;

                // check for unassigned variables used by the expression
                let used = expr.variable_deps();
                let unassigned: HashSet<usize> = used.difference(&vars).copied().collect();
                if !unassigned.is_empty() {
                    return Err(Error::UnassignedVariables(unassigned));
                }

                // confirm that the type of the expression matches the variable
                if got_ty != expected_ty {
                    return Err(Error::ExpectedType {
                        expected: expected_ty,
                        got: got_ty,
                    });
                }

                Ok(vars)
            }
            Merge(lhs, rhs) => {
                // validate each branch first
                let lhs = lhs.validate(relations, variables)?;
                let rhs = rhs.validate(relations, variables)?;

                // test for equality of the two sides
                if lhs == rhs {
                    Ok(lhs)
                } else {
                    // otherwise report an error
                    let lhs_only: HashSet<_> = lhs.difference(&rhs).copied().collect();
                    let rhs_only: HashSet<_> = rhs.difference(&lhs).copied().collect();
                    Err(Error::MergeVariableMismatch { lhs_only, rhs_only })
                }
            }
            Join(lhs, rhs) => {
                // just take the union of either branch
                let mut vars = lhs.validate(relations, variables)?;
                vars.extend(rhs.validate(relations, variables)?);
                Ok(vars)
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
                .get(*idx)
                .cloned()
                .ok_or(Error::InvalidVariableIndex(*idx)),
            Value(val) => Ok(val.ty()),
            Load { relation, query } => {
                if *relation >= relations.len() {
                    return Err(Error::InvalidRelationIndex(*relation));
                }

                for term in query {
                    match term {
                        QueryTerm::Variable(idx) => {
                            if *idx >= variables.len() {
                                return Err(Error::InvalidVariableIndex(*idx));
                            }
                        }
                        QueryTerm::Value(_) => {}
                    }
                }

                Ok(Type::Boolean)
            }
            UnaryOp { op, term } => {
                let term = term.validate(relations, variables)?;
                use Type::*;
                use UnaryOpKind::*;
                match (op, term) {
                    (Not, Boolean) => Ok(Boolean),
                    (Negate, Integer) => Ok(Integer),
                    (Negate, Real) => Ok(Real),
                    (op, term) => Err(Error::InvalidUnaryOp { op: *op, term }),
                }
            }
            BinaryOp { op, lhs, rhs } => {
                let lhs = lhs.validate(relations, variables)?;
                let rhs = rhs.validate(relations, variables)?;
                use Type::*;
                match (op.category(), lhs, rhs) {
                    (BinaryOpCategory::Arithmetic, Integer, Integer) => Ok(Integer),
                    (BinaryOpCategory::Arithmetic, Real, Real) => Ok(Real),
                    (BinaryOpCategory::String, String, String) => Ok(String),
                    (BinaryOpCategory::Logical, Boolean, Boolean) => Ok(Boolean),
                    (BinaryOpCategory::Comparison, lhs, rhs) if lhs == rhs => Ok(lhs),
                    (_, lhs, rhs) => Err(Error::InvalidBinaryOp { op: *op, lhs, rhs }),
                }
            }
        }
    }

    /// Retrieves the set of variables accessed by this expression.
    pub fn variable_deps(&self) -> HashSet<usize> {
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
