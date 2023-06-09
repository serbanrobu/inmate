use std::str::FromStr;

use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, alphanumeric1, char, multispace0, u8},
    combinator::{eof, map, recognize, value},
    error::Error,
    multi::{many0, many1, separated_list1},
    sequence::{delimited, pair, preceded, separated_pair, terminated, tuple},
    Finish, IResult,
};

use crate::{Expr, Lambda, Name};

fn parse_name(input: &str) -> IResult<&str, Name> {
    fn base(input: &str) -> IResult<&str, &str> {
        alt((alphanumeric1, tag("_"), tag("\'")))(input)
    }

    map(
        recognize(alt((
            pair(alpha1, many0(base)),
            pair(tag("_"), many1(base)),
        ))),
        str::to_owned,
    )(input)
}

fn parse_lambda(input: &str) -> IResult<&str, Lambda> {
    map(
        pair(
            preceded(
                pair(char('\\'), multispace0),
                alt((value(None, tag("_")), map(parse_name, Some))),
            ),
            preceded(ws(char('.')), parse_lambda_layer),
        ),
        |(x, b)| Lambda { x, b },
    )(input)
}

fn parse_atom(input: &str) -> IResult<&str, Expr> {
    let bool_type = value(Expr::BoolType, tag("Bool"));

    let ind_bool = map(
        preceded(
            pair(tag("indBool"), multispace0),
            parens(tuple((
                terminated(ws(parse_expr), char(',')),
                terminated(ws(parse_expr), char(',')),
                terminated(ws(parse_expr), char(',')),
                ws(parse_expr),
            ))),
        ),
        |(c_type, c_0, c_1, bool)| Expr::IndBool {
            c_type: Box::new(c_type),
            c_0: Box::new(c_0),
            c_1: Box::new(c_1),
            bool: Box::new(bool),
        },
    );

    let pair_layer = map(
        parens(ws(separated_list1(ws(char(',')), parse_expr))),
        |es| {
            es.into_iter()
                .rev()
                .reduce(|acc, e| Expr::Pair(Box::new(e), Box::new(acc)))
                .unwrap()
        },
    );

    let pi_type = map(
        preceded(
            pair(tag("Pi"), multispace0),
            parens(separated_pair(ws(parse_expr), char(','), ws(parse_lambda))),
        ),
        |(a_type, b_type)| Expr::PiType {
            a_type: Box::new(a_type),
            b_type: Box::new(b_type),
        },
    );

    let rec_w = map(
        preceded(
            pair(tag("recW"), multispace0),
            parens(tuple((
                terminated(ws(parse_expr), char(',')),
                terminated(ws(parse_expr), char(',')),
                ws(parse_expr),
            ))),
        ),
        |(e_type, e, w)| Expr::RecW {
            e_type: Box::new(e_type),
            e: Box::new(e),
            w: Box::new(w),
        },
    );

    let sigma_type = map(
        preceded(
            pair(tag("Sigma"), multispace0),
            parens(separated_pair(ws(parse_expr), char(','), ws(parse_expr))),
        ),
        |(a_type, b_type)| Expr::SigmaType {
            a_type: Box::new(a_type),
            b_type: Box::new(b_type),
        },
    );

    let sup = map(
        preceded(
            pair(tag("sup"), multispace0),
            parens(separated_pair(ws(parse_expr), char(','), ws(parse_expr))),
        ),
        |(a, u)| Expr::Sup {
            a: Box::new(a),
            u: Box::new(u),
        },
    );

    let unit = value(Expr::Unit, tag("unit"));
    let unit_type = value(Expr::UnitType, tag("Unit"));

    let u_type = map(
        preceded(pair(char('U'), multispace0), parens(ws(u8))),
        Expr::UType,
    );

    let void_ind = map(
        preceded(
            pair(tag("indVoid"), multispace0),
            parens(separated_pair(ws(parse_expr), char(','), ws(parse_expr))),
        ),
        |(c_type, void)| Expr::IndVoid {
            c_type: Box::new(c_type),
            void: Box::new(void),
        },
    );

    let void_type = value(Expr::VoidType, tag("Void"));

    let w_type = map(
        preceded(
            pair(char('W'), multispace0),
            parens(separated_pair(ws(parse_expr), char(','), ws(parse_expr))),
        ),
        |(a_type, b_type)| Expr::WType {
            a_type: Box::new(a_type),
            b_type: Box::new(b_type),
        },
    );

    let var = map(parse_name, Expr::Var);

    alt((
        bool_type,
        ind_bool,
        value(Expr::False, tag("false")),
        pair_layer,
        pi_type,
        rec_w,
        sigma_type,
        sup,
        value(Expr::True, tag("true")),
        unit,
        unit_type,
        u_type,
        void_ind,
        void_type,
        w_type,
        var,
    ))(input)
}

fn parse_application_layer(input: &str) -> IResult<&str, Expr> {
    map(
        separated_pair(
            parse_atom,
            multispace0,
            many0(parens(separated_list1(char(','), ws(parse_expr)))),
        ),
        |(function, arguments)| {
            arguments
                .into_iter()
                .flatten()
                .fold(function, |function, argument| Expr::Application {
                    function: Box::new(function),
                    argument: Box::new(argument),
                })
        },
    )(input)
}

fn parse_function_type_layer(input: &str) -> IResult<&str, Expr> {
    map(
        separated_list1(ws(tag("->")), parse_application_layer),
        |types| {
            types
                .into_iter()
                .rev()
                .reduce(|acc, e| Expr::PiType {
                    a_type: Box::new(e),
                    b_type: Box::new(Lambda { x: None, b: acc }),
                })
                .unwrap()
        },
    )(input)
}

fn parse_lambda_layer(input: &str) -> IResult<&str, Expr> {
    alt((
        map(parse_lambda, |lambda| Expr::Lambda(Box::new(lambda))),
        parse_function_type_layer,
    ))(input)
}

fn parse_expr(input: &str) -> IResult<&str, Expr> {
    parse_lambda_layer(input)
}

impl FromStr for Expr {
    type Err = Error<String>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (_remaining, checkable) = terminated(parse_expr, eof)(s.trim())
            .finish()
            .map_err(|e| Error::new(e.input.to_string(), e.code))?;

        Ok(checkable)
    }
}

fn parens<'a, F, O>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O>
where
    F: FnMut(&'a str) -> IResult<&'a str, O>,
{
    delimited(char('('), inner, char(')'))
}

fn ws<'a, F: 'a, O>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O>
where
    F: FnMut(&'a str) -> IResult<&'a str, O>,
{
    delimited(multispace0, inner, multispace0)
}
