use color_eyre::Result;
use inmate::{Context, Env, Expr, Level, Name, Neutral, Type, Value};
use rustyline::{config::Configurer, error::ReadlineError, EditMode};

fn main() -> Result<()> {
    let mut context = Context::new();
    let mut env = Env::new();

    let defs = [
        ("the", "Pi(U(254), \\A. A -> A)", Some("\\_. \\a. a")),
        (
            "recBool",
            "Pi(U(254), \\C. C -> C -> Bool -> C)",
            Some("\\C. \\c0. \\c1. \\b. indBool(\\_. C, c0, c1, b)"),
        ),
        (
            "recVoid",
            "Pi(U(254), \\C. Void -> C)",
            Some("\\C. \\x. indVoid(\\_. C, x)"),
        ),
        ("Command", "U(0)", None),
        ("quit", "Command", None),
        ("eval", "Pi(U(254), \\A. A -> Command)", None),
    ];

    for (name, r#type, term) in defs {
        let name = Name::from(name);
        let r#type: Expr = r#type.parse()?;
        r#type.check(&Type::UType(Level::MAX), &context, &env)?;
        let r#type = r#type.eval(&env);

        if let Some(term) = term {
            let term: Expr = term.parse()?;
            term.check(&r#type, &context, &env)?;
            env.insert(name.clone(), term.eval(&env));
        }

        context.insert(name, r#type);
    }

    let mut rl = rustyline::DefaultEditor::new()?;
    rl.set_edit_mode(EditMode::Vi);
    let r#type = Type::var(Name::from("Command"));

    loop {
        let result = rl.readline(">> ");

        match result {
            Ok(line) => {
                rl.add_history_entry(&line)?;

                match line.parse::<Expr>() {
                    Ok(expression) => match expression.check(&r#type, &context, &env) {
                        Ok(()) => {
                            let command = expression.eval(&env);

                            match command {
                                Value::Neutral(Neutral::Var(name)) => {
                                    let "quit" = name.as_str() else {
                                        unreachable!();
                                    };

                                    println!("Bye bye!");
                                    break;
                                }
                                Value::Neutral(Neutral::Application {
                                    function,
                                    argument: term,
                                }) => {
                                    let Neutral::Application { function, argument: r#type } = *function else {
                                        unreachable!();
                                    };

                                    let Neutral::Var(name) = *function else {
                                        unreachable!();
                                    };

                                    let "eval" = name.as_str() else {
                                        unreachable!();
                                    };

                                    println!("{term} : {type}");
                                }
                                _ => unreachable!(),
                            }
                        }
                        Err(e) => eprintln!("{e}"),
                    },
                    Err(e) => eprintln!("{e}"),
                }
            }
            Err(ReadlineError::Interrupted) => {
                println!("CTRL-C");
                break;
            }
            Err(ReadlineError::Eof) => {
                println!("CTRL-D");
                break;
            }
            Err(err) => {
                eprintln!("Error: {err}");
                break;
            }
        }
    }

    Ok(())
}
