mod lambda_core;
use lambda_core::{evaluate_expression, test_simple_cases, test_complex_case};
use std::collections::HashMap;
use std::io::{self, Write};

fn main() {
    // シンボル定義を作成
    let symbols = create_symbols();

    println!("=== Lambda計算インタープリター ===");
    println!("式を入力してください (例: (λx.x) y, succ 2, add 2 3)");
    println!("'quit' または 'exit' で終了");
    println!("'test' で組み込みテストを実行");
    println!();

    loop {
        print!("λ> ");
        io::stdout().flush().unwrap();

        let mut input = String::new();
        match io::stdin().read_line(&mut input) {
            Ok(_) => {
                let input = input.trim();

                if input.is_empty() {
                    continue;
                }

                if input == "quit" || input == "exit" {
                    println!("さようなら！");
                    break;
                } else if input == "test" {
                    test_simple_cases();
                    test_complex_case(&symbols);
                } else {
                    evaluate_expression(input.to_string(), &symbols);
                }
            }
            Err(e) => {
                println!("入力エラー: {}", e);
                break;
            }
        }
        println!();
    }
}

fn create_symbols() -> HashMap<String, String> {
    let mut symbols = HashMap::new();

    // ブール値
    symbols.insert("true".to_string(), "(λt.λf.t)".to_string());
    symbols.insert("false".to_string(), "(λt.λf.f)".to_string());

    // データ構造
    symbols.insert("pair".to_string(), "(λf.λs.λb.b f s)".to_string());
    symbols.insert("fst".to_string(), "(λp.p true)".to_string());
    symbols.insert("snd".to_string(), "(λp.p false)".to_string());

    // ブール演算
    symbols.insert("if".to_string(), "(λcond.λthen.λelse.cond then else)".to_string());
    symbols.insert("and".to_string(), "(λp.λq.p q false)".to_string());
    symbols.insert("or".to_string(), "(λp.λq.p true q)".to_string());
    symbols.insert("not".to_string(), "(λp.false true)".to_string());

    // Church数演算の定義
    symbols.insert("succ".to_string(), "(λn.λs.λz.s (n s z))".to_string());
    symbols.insert("add".to_string(), "(λm.λn.λs.λz.m s (n s z))".to_string());
    symbols.insert("prd".to_string(), "(λn.λs.λz.n (λg.λh.h (g s)) (λu.z) (λu.u))".to_string());
    symbols.insert("mul".to_string(), "(λm.λn.λf.m (n f))".to_string());
    symbols.insert("exp".to_string(), "(λm.λn.n m)".to_string());
    symbols.insert("tet".to_string(), "(λm.λn. (prd n) (exp m) m)".to_string());

    // Church数テスト用の関数
    symbols.insert("iszro".to_string(), "(λn.n (λx.false) true)".to_string());

    // 再帰
    symbols.insert("fix".to_string(), "(λf.(λx.f (x x)) (λx.f (x x)))".to_string());
    symbols.insert("omega".to_string(), "(λx.x x) (λx.x x)".to_string());

    // 階乗 (fact) : fact = fix (λf.λn. if (iszro n) c1 (mul n (f (prd n))))
    symbols.insert(
        "fact".to_string(),
        "(fix (λf.λn.if (iszro n) c1 (mul n (f (prd n)))))".to_string(),
    );

    symbols
}
