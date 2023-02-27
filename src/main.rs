// letter is an actual "letter" in a-math after blank designation
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Letter {
    Div,
    Mul,
    Sub,
    Add,
    Eql,
    N0,
    N1,
    N2,
    N3,
    N4,
    N5,
    N6,
    N7,
    N8,
    N9,
    N10,
    N11,
    N12,
    N13,
    N14,
    N15,
    N16,
    N17,
    N18,
    N19,
    N20,
}

const MAXLEN: usize = 15;

impl Letter {
    #[inline(always)]
    fn numeric_value(&self) -> i8 {
        match self {
            Self::Div | Self::Mul | Self::Sub | Self::Add | Self::Eql => -1,
            Self::N0 => 0,
            Self::N1 => 1,
            Self::N2 => 2,
            Self::N3 => 3,
            Self::N4 => 4,
            Self::N5 => 5,
            Self::N6 => 6,
            Self::N7 => 7,
            Self::N8 => 8,
            Self::N9 => 9,
            Self::N10 => 10,
            Self::N11 => 11,
            Self::N12 => 12,
            Self::N13 => 13,
            Self::N14 => 14,
            Self::N15 => 15,
            Self::N16 => 16,
            Self::N17 => 17,
            Self::N18 => 18,
            Self::N19 => 19,
            Self::N20 => 20,
        }
    }

    #[inline(always)]
    fn operator_priority(&self) -> i8 {
        match self {
            Self::Div | Self::Mul => 3,
            Self::Sub | Self::Add => 2,
            Self::Eql => 1,
            Self::N0
            | Self::N1
            | Self::N2
            | Self::N3
            | Self::N4
            | Self::N5
            | Self::N6
            | Self::N7
            | Self::N8
            | Self::N9
            | Self::N10
            | Self::N11
            | Self::N12
            | Self::N13
            | Self::N14
            | Self::N15
            | Self::N16
            | Self::N17
            | Self::N18
            | Self::N19
            | Self::N20 => 0,
        }
    }

    #[inline(always)]
    fn label(&self) -> &'static str {
        match self {
            Self::Div => "/",
            Self::Mul => "*",
            Self::Sub => "-",
            Self::Add => "+",
            Self::Eql => "=",
            Self::N0 => "0",
            Self::N1 => "1",
            Self::N2 => "2",
            Self::N3 => "3",
            Self::N4 => "4",
            Self::N5 => "5",
            Self::N6 => "6",
            Self::N7 => "7",
            Self::N8 => "8",
            Self::N9 => "9",
            Self::N10 => "[10]",
            Self::N11 => "[11]",
            Self::N12 => "[12]",
            Self::N13 => "[13]",
            Self::N14 => "[14]",
            Self::N15 => "[15]",
            Self::N16 => "[16]",
            Self::N17 => "[17]",
            Self::N18 => "[18]",
            Self::N19 => "[19]",
            Self::N20 => "[20]",
        }
    }
}

enum GenState {
    StartOfExpression,
    StartOfNumber,
    StartOfDivisor,
    AfterNumber,
    AfterOneNonzeroDigit,
    AfterTwoDigits,
}

fn gen_all() -> i64 {
    struct Env {
        buf: Vec<Letter>,
        start_idx: usize,
        known_n: i64,
        known_d: i64,
        num_stack: Vec<(i64, i64)>,
        op_stack: Vec<Letter>,
        num_found: i64,
    }

    // evaluates buf[start_idx..].
    // If start_idx is 0, write the result on known_n/known_d, and return true.
    // If not, compare the result with known_n/known_d. Return true iff same.
    // Assumes well-formed expr ([minus] num op num op num... with no Eql).
    #[inline(always)]
    fn expr_eval(env: &mut Env) -> bool {
        if false {
            return true;
        }
        let len = env.buf.len();
        let mut i = env.start_idx;
        env.num_stack.clear();
        env.op_stack.clear();
        loop {
            let is_negative = if let Letter::Sub = env.buf[i] {
                i += 1;
                true
            } else {
                false
            };
            let mut val = env.buf[i].numeric_value() as i32;
            i += 1;
            while i < len {
                let val2 = env.buf[i].numeric_value() as i32;
                if val2 >= 0 {
                    val = val * 10 + val2;
                    i += 1;
                } else {
                    break;
                }
            }
            if is_negative {
                val = -val;
            }
            env.num_stack.push((val as i64, 1i64));
            let op = if i < len { env.buf[i] } else { Letter::Eql };
            let op_prio = op.operator_priority();
            if !(env.op_stack.len() + 1 == env.num_stack.len()
                && (env.op_stack.is_empty()
                    || (env.op_stack.len() == 1
                        && (env.op_stack[0] == Letter::Add
                            || env.op_stack[0] == Letter::Sub
                            || env.op_stack[0] == Letter::Mul
                            || env.op_stack[0] == Letter::Div))
                    || (env.op_stack.len() == 2
                        && (env.op_stack[0] == Letter::Add || env.op_stack[0] == Letter::Sub)
                        && (env.op_stack[1] == Letter::Mul || env.op_stack[1] == Letter::Div))))
            {
                println!("{:?} {}", env.op_stack, env.num_stack.len());
                panic!();
                // this can be optimized?
                // it is always either [n1 Add/Sub] [n2 Mul/Div] curnum
                // if curop is Mul/Div/Add/Sub/Eq and n2 exists => resolve n2 with curnum
                // if curop is Add/Sub/Eq and n1 exists => resolve n1 with curnum
                // then if i >= len (this is eq) finalize curnum
                // else put curnum and curop as n1 or n2 as appropriate
            }
            while !env.op_stack.is_empty()
                && env.op_stack.last().unwrap().operator_priority() >= op_prio
            {
                let (n2, d2) = env.num_stack.pop().unwrap();
                let (n1, d1) = env.num_stack.pop().unwrap();
                match env.op_stack.pop().unwrap() {
                    Letter::Add => env.num_stack.push((n1 * d2 + n2 * d1, d1 * d2)),
                    Letter::Sub => env.num_stack.push((n1 * d2 - n2 * d1, d1 * d2)),
                    Letter::Mul => env.num_stack.push((n1 * n2, d1 * d2)),
                    Letter::Div => env.num_stack.push((n1 * d2, d1 * n2)),
                    _ => panic!("bad input"),
                }
            }
            if i >= len {
                let (n, d) = env.num_stack.pop().unwrap();
                if env.start_idx == 0 {
                    env.known_n = n;
                    env.known_d = d;
                } else if env.known_n * d != env.known_d * n {
                    return false;
                }
                return true;
            } else {
                env.op_stack.push(op);
                i += 1;
            }
        }
    }

    #[inline(always)]
    fn attempt(env: &mut Env, letter: Letter, next_state: GenState) {
        if env.buf.len() < MAXLEN {
            if let Letter::Eql = letter {
                // assume expr_eval(env)
                let x = env.start_idx;
                env.buf.push(letter);
                env.start_idx = env.buf.len();
                gen(env, next_state);
                env.buf.pop();
                env.start_idx = x;
            } else if env.start_idx != 0 || env.buf.len() < MAXLEN - 2 {
                env.buf.push(letter);
                gen(env, next_state);
                env.buf.pop();
            }
        }
    }

    fn gen(env: &mut Env, state: GenState) {
        if match state {
            GenState::StartOfExpression => true,
            GenState::StartOfNumber
            | GenState::StartOfDivisor
            | GenState::AfterNumber
            | GenState::AfterOneNonzeroDigit
            | GenState::AfterTwoDigits => false,
        } {
            attempt(env, Letter::Sub, GenState::StartOfNumber);
            // alt: on SoE if -ve go to NegSoN
        }
        if match state {
            GenState::StartOfExpression | GenState::StartOfNumber => true,
            GenState::StartOfDivisor
            | GenState::AfterNumber
            | GenState::AfterOneNonzeroDigit
            | GenState::AfterTwoDigits => false,
        } {
            // alt: on NegSoN 0 is same
            attempt(env, Letter::N0, GenState::AfterNumber);
        }
        if match state {
            GenState::StartOfExpression | GenState::StartOfNumber | GenState::StartOfDivisor => {
                true
            }
            GenState::AfterNumber | GenState::AfterOneNonzeroDigit | GenState::AfterTwoDigits => {
                false
            }
        } {
            // alt: on NegSoN 1-9 sets -1..-9 and goes to AfterNegatedOneNonzeroDigit
            // on NegSon 10-20 sets -10..-20 and done
            attempt(env, Letter::N1, GenState::AfterOneNonzeroDigit);
            attempt(env, Letter::N2, GenState::AfterOneNonzeroDigit);
            attempt(env, Letter::N3, GenState::AfterOneNonzeroDigit);
            attempt(env, Letter::N4, GenState::AfterOneNonzeroDigit);
            attempt(env, Letter::N5, GenState::AfterOneNonzeroDigit);
            attempt(env, Letter::N6, GenState::AfterOneNonzeroDigit);
            attempt(env, Letter::N7, GenState::AfterOneNonzeroDigit);
            attempt(env, Letter::N8, GenState::AfterOneNonzeroDigit);
            attempt(env, Letter::N9, GenState::AfterOneNonzeroDigit);
            attempt(env, Letter::N10, GenState::AfterNumber);
            attempt(env, Letter::N11, GenState::AfterNumber);
            attempt(env, Letter::N12, GenState::AfterNumber);
            attempt(env, Letter::N13, GenState::AfterNumber);
            attempt(env, Letter::N14, GenState::AfterNumber);
            attempt(env, Letter::N15, GenState::AfterNumber);
            attempt(env, Letter::N16, GenState::AfterNumber);
            attempt(env, Letter::N17, GenState::AfterNumber);
            attempt(env, Letter::N18, GenState::AfterNumber);
            attempt(env, Letter::N19, GenState::AfterNumber);
            attempt(env, Letter::N20, GenState::AfterNumber);
        }
        if match state {
            GenState::StartOfExpression | GenState::StartOfNumber | GenState::StartOfDivisor => {
                false
            }
            GenState::AfterNumber | GenState::AfterOneNonzeroDigit | GenState::AfterTwoDigits => {
                true
            }
        } {
            // alt: also on negated versions (temp i16 alr correct)
            // for all 5 ops resolve "n2 [Mul/Div] curnum"
            // for Add/Sub/Eq also resolve "n1 [Add/Sub] that"
            // Eq has addl check w/ prev eqn
            // so: (state, curnum:i16, additivenum:(i64,i64), additiveop:Opt<Add|Sub>, mulnum:, mulop:Opt<Mul|Div>)
            // (op can also be new enums w/ params only for non-none cases)
            // newmulnum:(i64,i64) = (curnum,1) when no mulop
            // (mulnum*curnum or mulnum/curnum) else.
            // attempt(s+Mul, SoN, 0, addnum, addop, newmulnum, Mul)
            // attempt(s+Div, SoD, 0, addnum, addop, newmulnum, Div)
            // newaddnum:(i64,i64) = newmulnum when no additiveop
            // (addnum+newmulnum or addnum-newmulnum) else.
            // attempt(s+Add, SoN, 0, newaddnum, Add, ignored, None)
            // attempt(s+Sub, SoN, 0, newaddnum, Sub, ignored, None)
            // if known is None { known = newaddnum; attempt(s+Eq, SoE, 0, -,None, -,None); known = None }
            // else if known.n * newaddnum.d == known.d * newaddnum.n { yield(expr);
            //   attempt(s+Eq, SoE, 0, -,None, -,None); }
            // (note: known is Opt<(i64,i64)> but stored in Env because it rarely changes)
            // note: attempt() checks length
            attempt(env, Letter::Add, GenState::StartOfNumber);
            attempt(env, Letter::Sub, GenState::StartOfNumber);
            attempt(env, Letter::Mul, GenState::StartOfNumber);
            attempt(env, Letter::Div, GenState::StartOfDivisor);
            if expr_eval(env) {
                if env.start_idx != 0 {
                    if true {
                        println!("{}", env.buf.iter().map(|x| x.label()).collect::<String>());
                    }
                    env.num_found += 1;
                }
                attempt(env, Letter::Eql, GenState::StartOfExpression);
            }
        }
        if match state {
            GenState::StartOfExpression
            | GenState::StartOfNumber
            | GenState::StartOfDivisor
            | GenState::AfterNumber
            | GenState::AfterTwoDigits => false,
            GenState::AfterOneNonzeroDigit => true,
        } {
            // alt: on AftNegOneNzDig 0-9 does *10-i and goes to AftNeg2Dig
            attempt(env, Letter::N0, GenState::AfterTwoDigits);
            attempt(env, Letter::N1, GenState::AfterTwoDigits);
            attempt(env, Letter::N2, GenState::AfterTwoDigits);
            attempt(env, Letter::N3, GenState::AfterTwoDigits);
            attempt(env, Letter::N4, GenState::AfterTwoDigits);
            attempt(env, Letter::N5, GenState::AfterTwoDigits);
            attempt(env, Letter::N6, GenState::AfterTwoDigits);
            attempt(env, Letter::N7, GenState::AfterTwoDigits);
            attempt(env, Letter::N8, GenState::AfterTwoDigits);
            attempt(env, Letter::N9, GenState::AfterTwoDigits);
        }
        if match state {
            GenState::StartOfExpression
            | GenState::StartOfNumber
            | GenState::StartOfDivisor
            | GenState::AfterNumber
            | GenState::AfterOneNonzeroDigit => false,
            GenState::AfterTwoDigits => true,
        } {
            // alt: on AftNegOneNzDig 0-9 does *10-i and done
            attempt(env, Letter::N0, GenState::AfterNumber);
            attempt(env, Letter::N1, GenState::AfterNumber);
            attempt(env, Letter::N2, GenState::AfterNumber);
            attempt(env, Letter::N3, GenState::AfterNumber);
            attempt(env, Letter::N4, GenState::AfterNumber);
            attempt(env, Letter::N5, GenState::AfterNumber);
            attempt(env, Letter::N6, GenState::AfterNumber);
            attempt(env, Letter::N7, GenState::AfterNumber);
            attempt(env, Letter::N8, GenState::AfterNumber);
            attempt(env, Letter::N9, GenState::AfterNumber);
        }
    }

    let mut env = Env {
        buf: Vec::new(),
        start_idx: 0,
        known_n: 0,
        known_d: 0,
        num_stack: Vec::new(),
        op_stack: Vec::new(),
        num_found: 0,
    };
    gen(&mut env, GenState::StartOfExpression);
    env.num_found
}

fn main() {
    println!("{}", gen_all());
}
