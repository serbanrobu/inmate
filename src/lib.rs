mod parser;

use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
    fmt,
};

use color_eyre::{
    eyre::{eyre, ContextCompat},
    Result,
};

#[derive(Clone, Debug)]
pub struct Closure(Env, Lambda);

impl Closure {
    pub fn application(self, argument: Value) -> Value {
        let Closure(mut env, Lambda { x, b }) = self;

        if let Some(x) = x {
            env.insert(x, argument);
        }

        b.eval(&env)
    }

    pub fn quote(&self, names: &HashSet<Name>) -> Lambda {
        let Closure(env, Lambda { x, b }) = self;

        let mut names = Cow::Borrowed(names);
        let mut env = Cow::Borrowed(env);

        let x = x.as_ref().map(|x| {
            let y = freshen(x.to_owned(), &names);
            names.to_mut().insert(y.clone());
            env.to_mut().insert(x.to_owned(), Value::var(y.clone()));
            y
        });

        let b = b.eval(&env).quote(&names);
        Lambda { x, b }
    }
}

#[derive(Clone, Debug, Eq)]
pub enum Expr {
    Application {
        function: Box<Expr>,
        argument: Box<Expr>,
    },
    BoolType,
    False,
    IndBool {
        c_type: Box<Expr>,
        c_0: Box<Expr>,
        c_1: Box<Expr>,
        bool: Box<Expr>,
    },
    IndVoid {
        c_type: Box<Expr>,
        void: Box<Expr>,
    },
    Lambda(Box<Lambda>),
    Pair(Box<Expr>, Box<Expr>),
    PiType {
        a_type: Box<Expr>,
        b_type: Box<Lambda>,
    },
    RecW {
        e_type: Box<Expr>,
        e: Box<Expr>,
        w: Box<Expr>,
    },
    SigmaType {
        a_type: Box<Expr>,
        b_type: Box<Expr>,
    },
    Sup {
        a: Box<Expr>,
        u: Box<Expr>,
    },
    True,
    UType(Level),
    Unit,
    UnitType,
    Var(Name),
    VoidType,
    WType {
        a_type: Box<Expr>,
        b_type: Box<Expr>,
    },
}

impl Expr {
    pub fn alpha_eq(&self, other: &Self, level_op: fn(&Level, &Level) -> bool) -> bool {
        let names = HashMap::new();
        self.alpha_eq_(other, 0, &names, &names, level_op)
    }

    fn alpha_eq_(
        &self,
        other: &Self,
        i: usize,
        names: &HashMap<Name, usize>,
        other_names: &HashMap<Name, usize>,
        level_op: fn(&Level, &Level) -> bool,
    ) -> bool {
        match (self, other) {
            (
                Self::Application { function, argument },
                Self::Application {
                    function: other_function,
                    argument: other_argument,
                },
            ) => {
                function.alpha_eq_(other_function, i, names, other_names, level_op)
                    && argument.alpha_eq_(other_argument, i, names, other_names, level_op)
            }
            (Self::BoolType, Self::BoolType) => true,
            (Self::False, Self::False) => true,
            (
                Self::IndBool {
                    c_type,
                    c_0,
                    c_1,
                    bool,
                },
                Self::IndBool {
                    c_type: other_c_type,
                    c_0: other_c_0,
                    c_1: other_c_1,
                    bool: other_bool,
                },
            ) => {
                bool.alpha_eq_(other_bool, i, names, other_names, level_op)
                    && c_type.alpha_eq_(other_c_type, i, names, other_names, level_op)
                    && c_0.alpha_eq_(other_c_0, i, names, other_names, level_op)
                    && c_1.alpha_eq_(other_c_1, i, names, other_names, level_op)
            }
            (
                Self::IndVoid { c_type, void },
                Self::IndVoid {
                    c_type: other_c_type,
                    void: other_void,
                },
            ) => {
                c_type.alpha_eq_(other_c_type, i, names, other_names, level_op)
                    && void.alpha_eq_(other_void, i, names, other_names, level_op)
            }
            (Self::Lambda(lambda), Self::Lambda(other_lambda)) => {
                lambda.alpha_eq_(other_lambda, i, names, other_names, level_op)
            }
            (Self::Pair(a, b), Self::Pair(other_a, other_b)) => {
                a.alpha_eq_(other_a, i, names, other_names, level_op)
                    && b.alpha_eq_(other_b, i, names, other_names, level_op)
            }
            (
                Self::PiType { a_type, b_type },
                Self::PiType {
                    a_type: other_a_type,
                    b_type: other_b_type,
                },
            ) => {
                a_type.alpha_eq_(other_a_type, i, names, other_names, level_op)
                    && b_type.alpha_eq_(other_b_type, i, names, other_names, level_op)
            }
            (
                Self::RecW { e_type, e, w },
                Self::RecW {
                    e_type: other_e_type,
                    e: other_e,
                    w: other_w,
                },
            ) => {
                e_type.alpha_eq_(other_e_type, i, names, other_names, level_op)
                    && e.alpha_eq_(other_e, i, names, other_names, level_op)
                    && w.alpha_eq_(other_w, i, names, other_names, level_op)
            }
            (
                Self::SigmaType { a_type, b_type },
                Self::SigmaType {
                    a_type: other_a_type,
                    b_type: other_b_type,
                },
            ) => {
                a_type.alpha_eq_(other_a_type, i, names, other_names, level_op)
                    && b_type.alpha_eq_(other_b_type, i, names, other_names, level_op)
            }
            (
                Self::Sup { a, u },
                Self::Sup {
                    a: other_a,
                    u: other_u,
                },
            ) => {
                a.alpha_eq_(other_a, i, names, other_names, level_op)
                    && u.alpha_eq_(other_u, i, names, other_names, level_op)
            }
            (Self::True, Self::True) => true,
            (Self::Unit, Self::Unit) => true,
            (Self::UnitType, Self::UnitType) => true,
            (Self::UType(level), Self::UType(other_level)) => level_op(level, other_level),
            (Self::Var(x), Self::Var(other_x)) => match (names.get(x), other_names.get(other_x)) {
                (None, None) => x == other_x,
                (Some(j), Some(k)) => j == k,
                _ => false,
            },
            (Self::VoidType, Self::VoidType) => true,
            (
                Self::WType { a_type, b_type },
                Self::WType {
                    a_type: other_a_type,
                    b_type: other_b_type,
                },
            ) => {
                a_type.alpha_eq_(other_a_type, i, names, other_names, level_op)
                    && b_type.alpha_eq_(other_b_type, i, names, other_names, level_op)
            }
            _ => false,
        }
    }

    pub fn check(&self, r#type: &Type, context: &Context, env: &Env) -> Result<()> {
        match self {
            Self::BoolType => {
                let Type::UType(_) = r#type else {
                    return Err(eyre!("expected a term of type {type}, found {self}"));
                };

                Ok(())
            }
            Self::False => {
                let Type::BoolType = r#type else {
                    return Err(eyre!("expected a term of type {type}, found {self}"));
                };

                Ok(())
            }
            Self::Lambda(lambda) => {
                let Type::PiType { a_type, b_type } = r#type else {
                    return Err(eyre!("expected a term of type {type}, found {self}"));
                };

                lambda.check(
                    a_type.as_ref().to_owned(),
                    b_type.to_owned(),
                    context.to_owned(),
                    env,
                )
            }
            Self::Pair(a, b) => {
                let Type::SigmaType { a_type, b_type } = r#type else {
                    return Err(eyre!("expected a term of type {type}, found {self}"));
                };

                a.check(a_type, context, env)?;
                b.check(&b_type.to_owned().application(a.eval(env)), context, env)
            }
            Self::PiType { a_type, b_type } => {
                let &Type::UType(i) = r#type else {
                    return Err(eyre!("expected a term of type {type}, found {self}"));
                };

                a_type.check(r#type, context, env)?;

                b_type.check(
                    a_type.eval(env),
                    Closure(
                        Env::new(),
                        Lambda {
                            x: None,
                            b: Self::UType(i),
                        },
                    ),
                    context.to_owned(),
                    env,
                )
            }
            Self::SigmaType { a_type, b_type } => {
                let &Type::UType(i) = r#type else {
                    return Err(eyre!("expected a term of type {type}, found {self}"));
                };

                a_type.check(r#type, context, env)?;

                b_type.check(
                    &Type::PiType {
                        a_type: Box::new(a_type.eval(env)),
                        b_type: Closure(
                            Env::new(),
                            Lambda {
                                x: None,
                                b: Self::UType(i),
                            },
                        ),
                    },
                    context,
                    env,
                )
            }
            Self::Sup { a, u } => {
                let Type::WType { a_type, b_type } = r#type else {
                    return Err(eyre!("expected a term of type {type}, found {self}"));
                };

                a.check(a_type, context, env)?;
                let names = context.keys().cloned().collect();

                u.check(
                    &Type::PiType {
                        a_type: Box::new(b_type.to_owned().application(a.eval(env))),
                        b_type: Closure(
                            Env::new(),
                            Lambda {
                                x: None,
                                b: r#type.quote(&names),
                            },
                        ),
                    },
                    context,
                    env,
                )
            }
            Self::True => {
                let Type::BoolType = r#type else {
                    return Err(eyre!("expected a term of type {type}, found {self}"));
                };

                Ok(())
            }
            Self::Unit => {
                let Type::UnitType = r#type else {
                    return Err(eyre!("expected a term of type {type}, found {self}"));
                };

                Ok(())
            }
            Self::UnitType => {
                let Type::UType(_) = r#type else {
                    return Err(eyre!("expected a term of type {type}, found {self}"));
                };

                Ok(())
            }
            &Self::UType(i) => {
                let &Type::UType(j) = r#type else {
                    return Err(eyre!("expected a term of type {type}, found {self}"));
                };

                if i >= j {
                    return Err(eyre!("expected a universe level less then {j}, found {i}"));
                }

                Ok(())
            }
            Self::VoidType => {
                let Type::UType(_) = r#type else {
                    return Err(eyre!("expected a term of type {type}, found {self}"));
                };

                Ok(())
            }
            Self::WType { a_type, b_type } => {
                let &Type::UType(i) = r#type else {
                    return Err(eyre!("expected a term of type {type}, found {self}"));
                };

                a_type.check(r#type, context, env)?;

                b_type.check(
                    &Type::PiType {
                        a_type: Box::new(a_type.eval(env)),
                        b_type: Closure(
                            Env::new(),
                            Lambda {
                                x: None,
                                b: Self::UType(i),
                            },
                        ),
                    },
                    context,
                    env,
                )
            }
            Self::Application { .. }
            | Self::IndBool { .. }
            | Self::IndVoid { .. }
            | Self::RecW { .. }
            | Self::Var(_) => {
                let names = context.keys().cloned().collect();
                let inferred = self.infer(context, env)?;

                if !inferred
                    .quote(&names)
                    .alpha_eq(&r#type.quote(&names), Level::le)
                {
                    return Err(eyre!(
                        "expected a term of type {type}, found {self} : {inferred}"
                    ));
                }

                Ok(())
            }
        }
    }

    pub fn eval(&self, env: &Env) -> Value {
        match self {
            Self::Application { function, argument } => {
                function.eval(env).application(argument.eval(env))
            }
            Self::BoolType => Value::BoolType,
            Self::False => Value::False,
            Self::IndBool {
                bool,
                c_type,
                c_0,
                c_1,
            } => match bool.eval(env) {
                Value::False => c_0.eval(env),
                Value::True => c_1.eval(env),
                Value::Neutral(bool) => Value::Neutral(Neutral::IndBool {
                    c_type: Box::new(c_type.eval(env)),
                    c_0: Box::new(c_0.eval(env)),
                    c_1: Box::new(c_1.eval(env)),
                    bool: Box::new(bool),
                }),
                _ => unreachable!(),
            },
            Self::IndVoid { c_type, void } => {
                Value::ind_void(Box::new(c_type.eval(env)), void.eval(env))
            }
            Self::Lambda(lambda) => Value::Closure(lambda.to_owned().eval(env.to_owned())),
            Self::Pair(a, b) => Value::Pair(Box::new(a.eval(env)), Box::new(b.eval(env))),
            Self::PiType { a_type, b_type } => Value::PiType {
                a_type: Box::new(a_type.eval(env)),
                b_type: b_type.to_owned().eval(env.to_owned()),
            },
            Self::RecW { e_type, e, w } => {
                let Value::Sup { a, u: f } = w.eval(env) else {
                    panic!("expected a term of type W, found {w}");
                };

                // e(a, f, \b. recW(E, e, f(b)))
                e.eval(env)
                    .application(*a)
                    .application((*f).clone())
                    .application(Value::Closure(Closure(
                        env.to_owned(),
                        Lambda {
                            x: Some(Name::from("b")),
                            b: Self::RecW {
                                e_type: e_type.to_owned(),
                                e: e.to_owned(),
                                w: Box::new(Self::Application {
                                    function: Box::new(f.quote(&HashSet::new())),
                                    argument: Box::new(Self::Var(Name::from("b"))),
                                }),
                            },
                        },
                    )))
            }
            Self::SigmaType { a_type, b_type } => Value::SigmaType {
                a_type: Box::new(a_type.eval(env)),
                b_type: Box::new(b_type.eval(env)),
            },
            Self::Sup { a, u } => Value::Sup {
                a: Box::new(a.eval(env)),
                u: Box::new(u.eval(env)),
            },
            Self::True => Value::True,
            Self::Unit => Value::Unit,
            Self::UnitType => Value::UnitType,
            &Self::UType(level) => Value::UType(level),
            Self::Var(x) => env
                .get(x)
                .cloned()
                .unwrap_or_else(|| Value::var(x.to_owned())),
            Self::VoidType => Value::VoidType,
            Self::WType { a_type, b_type } => Value::WType {
                a_type: Box::new(a_type.eval(env)),
                b_type: Box::new(b_type.eval(env)),
            },
        }
    }

    pub fn fmt_parens(&self, f: &mut fmt::Formatter<'_>, cond: bool) -> fmt::Result {
        if cond {
            write!(f, "({self})")
        } else {
            write!(f, "{self}")
        }
    }

    pub fn infer(&self, context: &Context, env: &Env) -> Result<Type> {
        match self {
            Self::Application { function, argument } => {
                let function_type = function.infer(context, env)?;

                let Type::PiType { a_type, b_type } = function_type else {
                    return Err(eyre!("not a Function"));
                };

                argument.check(&a_type, context, env)?;
                let argument = argument.eval(env);
                Ok(b_type.application(argument))
            }
            Self::IndBool {
                c_type,
                c_0,
                c_1,
                bool,
            } => {
                let bool_type = bool.infer(context, env)?;

                let Type::BoolType = &bool_type else {
                    return Err(eyre!("not a Bool"));
                };

                c_type.check(
                    &Type::PiType {
                        a_type: Box::new(bool_type),
                        b_type: Closure(
                            Env::new(),
                            Lambda {
                                x: None,
                                b: Self::UType(Level::MAX),
                            },
                        ),
                    },
                    context,
                    env,
                )?;

                let c_type = c_type.eval(env);
                c_0.check(&c_type.clone().application(Value::False), context, env)?;
                c_1.check(&c_type.clone().application(Value::True), context, env)?;
                Ok(c_type.application(bool.eval(env)))
            }
            Self::IndVoid { c_type, void } => {
                let void_type = void.infer(context, env)?;

                let Type::VoidType = &void_type else {
                    return Err(eyre!("expected a term of type Void, found {void} : {void_type}"));
                };

                c_type.check(
                    &Type::PiType {
                        a_type: Box::new(void_type),
                        b_type: Closure(
                            Env::new(),
                            Lambda {
                                x: None,
                                b: Self::UType(Level::MAX),
                            },
                        ),
                    },
                    context,
                    env,
                )?;

                Ok(c_type.eval(env).application(void.eval(env)))
            }
            Self::RecW { e_type, e, w } => {
                let w_type = w.infer(context, env)?;
                let w = w.eval(env);

                let Type::WType { a_type, b_type } = &w_type else {
                    return Err(eyre!("expected a term of type W, found {w} : {w_type}"));
                };

                e_type.check(
                    &Type::PiType {
                        a_type: Box::new(w_type.clone()),
                        b_type: Closure(
                            Env::new(),
                            Lambda {
                                x: None,
                                b: Self::UType(Level::MAX),
                            },
                        ),
                    },
                    context,
                    env,
                )?;

                let names = context.keys().cloned().collect();
                let b_type = b_type.quote(&names);

                // Pi(
                //    A,
                //    \a. Pi(
                //        B(a) -> W(A, B),
                //        \f. Pi(B(a), \b. E(f(b))) -> E(sup(a, f))
                //    )
                // )
                e.check(
                    &Type::PiType {
                        a_type: Box::new(a_type.as_ref().to_owned()),
                        b_type: Closure(
                            env.to_owned(),
                            Lambda {
                                x: Some(Name::from("a")),
                                b: Self::PiType {
                                    a_type: Box::new(Self::PiType {
                                        a_type: Box::new(Self::Application {
                                            function: Box::new(b_type.clone()),
                                            argument: Box::new(Self::Var(Name::from("a"))),
                                        }),
                                        b_type: Box::new(Lambda {
                                            x: None,
                                            b: w_type.quote(&names),
                                        }),
                                    }),
                                    b_type: Box::new(Lambda {
                                        x: Some(Name::from("f")),
                                        b: Self::PiType {
                                            a_type: Box::new(Self::PiType {
                                                a_type: Box::new(Self::Application {
                                                    function: Box::new(b_type),
                                                    argument: Box::new(Self::Var(Name::from("a"))),
                                                }),
                                                b_type: Box::new(Lambda {
                                                    x: Some(Name::from("b")),
                                                    b: Self::Application {
                                                        function: e_type.to_owned(),
                                                        argument: Box::new(Self::Application {
                                                            function: Box::new(Self::Var(
                                                                Name::from("f"),
                                                            )),
                                                            argument: Box::new(Self::Var(
                                                                Name::from("b"),
                                                            )),
                                                        }),
                                                    },
                                                }),
                                            }),
                                            b_type: Box::new(Lambda {
                                                x: None,
                                                b: Self::Application {
                                                    function: e_type.to_owned(),
                                                    argument: Box::new(Self::Sup {
                                                        a: Box::new(Self::Var(Name::from("a"))),
                                                        u: Box::new(Self::Var(Name::from("f"))),
                                                    }),
                                                },
                                            }),
                                        },
                                    }),
                                },
                            },
                        ),
                    },
                    context,
                    env,
                )?;

                Ok(e_type.eval(env).application(w))
            }
            Self::Var(x) => context
                .get(x)
                .cloned()
                .wrap_err_with(|| eyre!("{x} not found")),
            _ => Err(eyre!("could not infer")),
        }
    }

    pub fn precedence(&self) -> Precedence {
        match self {
            Self::Application { .. } => Precedence::Application,
            Self::BoolType => Precedence::Atom,
            Self::False => Precedence::Atom,
            Self::IndBool { .. } => Precedence::Atom,
            Self::IndVoid { .. } => Precedence::Atom,
            Self::Lambda { .. } => Precedence::Lambda,
            Self::Pair(_, _) => Precedence::Atom,
            Self::PiType { .. } => Precedence::Atom,
            Self::RecW { .. } => Precedence::Atom,
            Self::SigmaType { .. } => Precedence::Atom,
            Self::Sup { .. } => Precedence::Atom,
            Self::True => Precedence::Atom,
            Self::Unit => Precedence::Atom,
            Self::UnitType => Precedence::Atom,
            Self::UType(_) => Precedence::Atom,
            Self::Var(_) => Precedence::Atom,
            Self::VoidType => Precedence::Atom,
            Self::WType { .. } => Precedence::Atom,
        }
    }
}

impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        self.alpha_eq(other, Level::eq)
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Application {
                function: func,
                argument,
            } => {
                let mut function: &Self = func;
                let mut arguments = vec![];

                loop {
                    match function {
                        Self::Application {
                            function: func,
                            argument: arg,
                        } => {
                            arguments.push(arg);
                            function = func;
                        }
                        Self::Var(x) => {
                            write!(f, "{x}(")?;
                            break;
                        }
                        _ => {
                            write!(f, "({function})(")?;
                            break;
                        }
                    }
                }

                for argument in arguments.into_iter().rev() {
                    write!(f, "{argument}, ")?;
                }

                write!(f, "{argument})")
            }
            Self::BoolType => "Bool".fmt(f),
            Self::False => "false".fmt(f),
            Self::IndBool {
                c_type,
                c_0,
                c_1,
                bool,
            } => write!(f, "indBool({c_type}, {c_0}, {c_1}, {bool})"),
            Self::IndVoid { c_type, void } => write!(f, "indVoid({c_type}, {void})"),
            Self::Lambda(lambda) => lambda.fmt(f),
            Self::Pair(a, b) => write!(f, "({a}, {b})"),
            Self::PiType { a_type, b_type } => write!(f, "Pi({a_type}, {b_type})"),
            Self::RecW { e_type, e, w } => write!(f, "recW({e_type}, {e}, {w})"),
            Self::SigmaType { a_type, b_type } => write!(f, "Sigma({a_type}, {b_type})"),
            Self::Sup { a, u } => write!(f, "sup({a}, {u})"),
            Self::True => "true".fmt(f),
            Self::Unit => "unit".fmt(f),
            Self::UnitType => "Unit".fmt(f),
            Self::UType(level) => write!(f, "U({level})"),
            Self::Var(x) => x.fmt(f),
            Self::VoidType => "Void".fmt(f),
            Self::WType { a_type, b_type } => write!(f, "W({a_type}, {b_type})"),
        }
    }
}

pub type Context = HashMap<Name, Type>;

pub type Env = HashMap<Name, Value>;

pub fn freshen(mut name: Name, names: &HashSet<Name>) -> Name {
    if names.contains(&name) {
        name.push('\'');
        freshen(name, names)
    } else {
        name
    }
}

pub fn fmt_context(context: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut iter = context.iter();

    write!(f, "(")?;

    match iter.next() {
        None => {}
        Some((name, r#type)) => {
            write!(f, "{name} : {type}")?;

            for (name, r#type) in context {
                write!(f, ", {name} : {type}")?;
            }
        }
    }

    write!(f, ")")?;

    Ok(())
}

#[derive(Clone, Debug, Eq)]
pub struct Lambda {
    x: Option<Name>,
    b: Expr,
}

impl Lambda {
    pub fn alpha_eq(&self, other: &Self, level_op: fn(&Level, &Level) -> bool) -> bool {
        let names = HashMap::new();
        self.alpha_eq_(other, 0, &names, &names, level_op)
    }

    fn alpha_eq_(
        &self,
        other: &Self,
        i: usize,
        names: &HashMap<Name, usize>,
        other_names: &HashMap<Name, usize>,
        level_op: fn(&Level, &Level) -> bool,
    ) -> bool {
        let (
            Self { x, b },
            Self {
                x: other_x,
                b: other_b,
            },
        ) = (self, other);

        let mut names = Cow::Borrowed(names);

        if let Some(x) = x {
            names.to_mut().insert(x.to_owned(), i);
        }

        let mut other_names = Cow::Borrowed(other_names);

        if let Some(other_x) = other_x {
            other_names.to_mut().insert(other_x.to_owned(), i);
        }

        b.alpha_eq_(other_b, i + 1, &names, &other_names, level_op)
    }

    pub fn check(
        &self,
        a_type: Type,
        b_type: Closure,
        mut context: Context,
        env: &Env,
    ) -> Result<()> {
        let Lambda { x, b } = self;

        let b_type = if let Some(x) = x {
            context.insert(x.to_owned(), a_type);
            b_type.application(Value::var(x.to_owned()))
        } else {
            let Closure(env, Lambda { x, b }) = b_type;

            if let Some(x) = x {
                context.insert(x, a_type);
            }

            b.eval(&env)
        };

        b.check(&b_type, &context, env)
    }

    pub fn eval(self, env: Env) -> Closure {
        Closure(env, self)
    }
}

impl fmt::Display for Lambda {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Lambda { x, b } = self;

        write!(
            f,
            "\\{}. {b}",
            x.as_ref().map(String::as_str).unwrap_or("_")
        )
    }
}

impl PartialEq for Lambda {
    fn eq(&self, other: &Self) -> bool {
        self.alpha_eq(other, Level::eq)
    }
}

pub type Level = u8;

pub type Name = String;

#[derive(Clone, Debug)]
pub enum Neutral {
    Application {
        function: Box<Neutral>,
        argument: Box<Value>,
    },
    IndBool {
        c_type: Box<Value>,
        c_0: Box<Value>,
        c_1: Box<Value>,
        bool: Box<Neutral>,
    },
    IndVoid {
        c_type: Box<Value>,
        void: Box<Neutral>,
    },
    Var(Name),
}

impl Neutral {
    fn quote(&self, names: &HashSet<Name>) -> Expr {
        match self {
            Self::Application { function, argument } => Expr::Application {
                function: Box::new(function.quote(names)),
                argument: Box::new(argument.quote(names)),
            },
            Self::IndBool {
                c_type,
                c_0,
                c_1,
                bool,
            } => Expr::IndBool {
                c_type: Box::new(c_type.quote(names)),
                c_1: Box::new(c_1.quote(names)),
                c_0: Box::new(c_0.quote(names)),
                bool: Box::new(bool.quote(names)),
            },
            Self::IndVoid { c_type, void } => Expr::IndVoid {
                c_type: Box::new(c_type.quote(names)),
                void: Box::new(void.quote(names)),
            },
            Self::Var(x) => Expr::Var(x.to_owned()),
        }
    }
}

#[derive(Eq, Ord, PartialEq, PartialOrd)]
pub enum Precedence {
    Lambda,
    Function,
    Application,
    Atom,
}

pub type Type = Value;

#[derive(Clone, Debug)]
pub enum Value {
    BoolType,
    False,
    Closure(Closure),
    Neutral(Neutral),
    Pair(Box<Value>, Box<Value>),
    PiType {
        a_type: Box<Value>,
        b_type: Closure,
    },
    SigmaType {
        a_type: Box<Value>,
        b_type: Box<Value>,
    },
    Sup {
        a: Box<Value>,
        u: Box<Value>,
    },
    True,
    UType(Level),
    Unit,
    UnitType,
    VoidType,
    WType {
        a_type: Box<Value>,
        b_type: Box<Value>,
    },
}

impl Value {
    pub fn application(self, argument: Self) -> Self {
        match self {
            Value::Closure(closure) => closure.application(argument),
            Value::Neutral(neutral) => Value::Neutral(Neutral::Application {
                function: Box::new(neutral),
                argument: Box::new(argument),
            }),
            _ => panic!("invalid application"),
        }
    }

    pub fn quote(&self, names: &HashSet<Name>) -> Expr {
        match self {
            Self::BoolType => Expr::BoolType,
            Self::False => Expr::False,
            Self::Closure(closure) => {
                let Lambda { x, b } = closure.quote(names);

                if let Some(x) = x {
                    if let Expr::Application { function, argument } = b {
                        if let Expr::Var(name) = argument.as_ref() {
                            if name == &x {
                                return *function;
                            }
                        }

                        return Expr::Lambda(Box::new(Lambda {
                            x: Some(x),
                            b: Expr::Application { function, argument },
                        }));
                    }

                    return Expr::Lambda(Box::new(Lambda { x: Some(x), b }));
                }

                Expr::Lambda(Box::new(Lambda { x: None, b }))
            }
            Self::Neutral(neutral) => neutral.quote(names),
            Self::Pair(a, b) => Expr::Pair(Box::new(a.quote(names)), Box::new(b.quote(names))),
            Self::PiType { a_type, b_type } => Expr::PiType {
                a_type: Box::new(a_type.quote(names)),
                b_type: Box::new(b_type.quote(names)),
            },
            Self::SigmaType { a_type, b_type } => Expr::SigmaType {
                a_type: Box::new(a_type.quote(names)),
                b_type: Box::new(b_type.quote(names)),
            },
            Self::Sup { a, u } => Expr::Sup {
                a: Box::new(a.quote(names)),
                u: Box::new(u.quote(names)),
            },
            Self::True => Expr::True,
            Self::Unit => Expr::Unit,
            Self::UnitType => Expr::UnitType,
            &Self::UType(level) => Expr::UType(level),
            Self::VoidType => Expr::VoidType,
            Self::WType { a_type, b_type } => Expr::WType {
                a_type: Box::new(a_type.quote(names)),
                b_type: Box::new(b_type.quote(names)),
            },
        }
    }

    pub fn var(x: Name) -> Self {
        Self::Neutral(Neutral::Var(x))
    }

    fn ind_void(c_type: Box<Self>, void: Self) -> Self {
        let Self::Neutral(void) = void else {
            unreachable!();
        };

        Self::Neutral(Neutral::IndVoid {
            c_type,
            void: Box::new(void),
        })
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.quote(&HashSet::new()).fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use color_eyre::Result;

    use super::*;

    #[test]
    fn it_works() -> Result<()> {
        let mut env = Env::new();

        let context = Context::from([
            (
                Name::from("f"),
                "U(0) -> U(0) -> U(0)".parse::<Expr>()?.eval(&env),
            ),
            (Name::from("y"), Type::UType(0)),
        ]);

        env.insert(Name::from("f"), "\\x. \\y. x".parse::<Expr>()?.eval(&env));

        let term: Expr = "f(y)".parse()?;
        let names = context.keys().cloned().collect();
        term.infer(&context, &env)?;
        let value = term.eval(&env);
        let expected: Expr = "\\y'. y".parse()?;

        assert_eq!(value.quote(&names), expected);

        Ok(())
    }

    #[test]
    fn pq_nq_np() -> Result<()> {
        let context = Context::from([
            (Name::from("Void"), Type::UType(0)),
            (
                Name::from("Not"),
                Type::PiType {
                    a_type: Box::new(Type::UType(0)),
                    b_type: Closure(
                        Env::new(),
                        Lambda {
                            x: None,
                            b: Expr::UType(0),
                        },
                    ),
                },
            ),
            (Name::from("P"), Type::UType(0)),
            (Name::from("Q"), Type::UType(0)),
        ]);

        let mut env = Env::new();

        env.insert(
            Name::from("Not"),
            "\\A. A -> Void".parse::<Expr>()?.eval(&env),
        );

        let r#type: Expr = "(P -> Q) -> Not(Q) -> Not(P)".parse()?;
        r#type.check(&Type::UType(0), &context, &env)?;
        let r#type = r#type.eval(&env);

        let term: Expr = "\\pq. \\nq. \\p. nq(pq(p))".parse()?;
        term.check(&r#type, &context, &env)?;

        Ok(())
    }
}
