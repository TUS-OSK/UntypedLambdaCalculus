use std::collections::HashSet;
use regex::Regex;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    Var(String),
    Lambda(String, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
}

pub fn collect_vars(expr: &Expr) -> HashSet<String> {
    let mut vars = HashSet::new();
    match expr {
        Expr::Var(v) => { vars.insert(v.clone()); },
        Expr::Lambda(p, body) => {
            vars.insert(p.clone());
            vars.extend(collect_vars(body));
        },
        Expr::App(f, x) => {
            vars.extend(collect_vars(f));
            vars.extend(collect_vars(x));
        }
    }
    vars
}

pub fn free_vars(expr: &Expr) -> HashSet<String> {
    match expr {
        Expr::Var(v) => {
            let mut s = HashSet::new();
            s.insert(v.clone());
            s
        }
        Expr::App(f, x) => {
            let mut s = free_vars(f);
            s.extend(free_vars(x));
            s
        }
        Expr::Lambda(p, body) => {
            let mut s = free_vars(body);
            s.remove(p);
            s
        }
    }
}

pub fn is_church_numeral(expr: &Expr) -> Option<usize> {
    if let Expr::Lambda(f, body) = expr {
        if let Expr::Lambda(x, body) = &**body {
            let mut count = 0;
            let mut cur = &**body;
            loop {
                match cur {
                    Expr::App(f_app, arg) => {
                        if let Expr::Var(f2) = &**f_app {
                            if f2 == f {
                                count += 1;
                                cur = &**arg;
                                continue;
                            }
                        }
                        break;
                    }
                    Expr::Var(x2) => {
                        if x2 == x {
                            return Some(count);
                        }
                        break;
                    }
                    _ => break,
                }
            }
        }
    }
    None
}

pub fn substitute(expr: &Expr, param: &str, value: &Expr) -> Expr {
    match expr {
        Expr::Var(v) => if v == param { value.clone() } else { Expr::Var(v.clone()) },
        Expr::App(f, x) => Expr::App(Box::new(substitute(f, param, value)), Box::new(substitute(x, param, value))),
        Expr::Lambda(p, body) => {
            if p == param {
                Expr::Lambda(p.clone(), body.clone())
            } else {
                // Only rename the lambda parameter if it appears free in the value being
                // substituted; otherwise renaming is unnecessary and harmful.
                let value_free = free_vars(value);
                if value_free.contains(p) {
                    // avoid collisions with variables in value or in the body
                    let mut occupied = collect_vars(value);
                    occupied.extend(collect_vars(body));
                    let mut idx = 1;
                    let mut new_p = format!("{}{}", p, idx);
                    while occupied.contains(&new_p) {
                        idx += 1;
                        new_p = format!("{}{}", p, idx);
                    }
                    let renamed_body = substitute(body, p, &Expr::Var(new_p.clone()));
                    Expr::Lambda(new_p, Box::new(substitute(&renamed_body, param, value)))
                } else {
                    Expr::Lambda(p.clone(), Box::new(substitute(body, param, value)))
                }
            }
        }
    }
}

pub fn beta_reduce_full(expr: &Expr) -> Expr {
    let mut e = expr.clone();
    let mut seen = HashSet::new();
    let max_steps = 100000; // ステップ数を増やす
    let mut steps = 0;

    while let Some(next) = beta_reduce_once_normal(&e) {
        steps += 1;
        let expr_str = to_string_expr(&e);
        if seen.contains(&expr_str) {
            println!("警告: 無限ループを検出しました（同じ式が繰り返されています）");
            println!("途中結果: {}", expr_str);
            break;
        }
        seen.insert(expr_str);
        if steps >= max_steps {
            println!("警告: 最大簡約ステップ数({})に到達しました", max_steps);
            println!("途中結果: {}", to_string_expr(&e));
            break;
        }
        e = next;
    }
    if steps > 0 {
        println!("簡約ステップ数: {}", steps);
    }
    e
}

// 段階的なβ簡約（指定ステップ数だけ計算）
pub fn beta_reduce_steps(expr: &Expr, max_steps: usize) -> Expr {
    let mut e = expr.clone();
    let mut seen = HashSet::new();
    let mut steps = 0;

    while let Some(next) = beta_reduce_once_normal(&e) && steps < max_steps {
        steps += 1;
        let expr_str = to_string_expr(&e);
        if seen.contains(&expr_str) {
            println!("警告: 無限ループを検出しました（同じ式が繰り返されています）");
            println!("途中結果: {}", expr_str);
            break;
        }
        seen.insert(expr_str);
        e = next;
    }

    println!("実行した簡約ステップ数: {}", steps);
    e
}

// 正規順序簡約（normal order reduction）
// 最も左の最も外側のβ-redexを簡約
pub fn beta_reduce_once_normal(expr: &Expr) -> Option<Expr> {
    match expr {
        Expr::App(f, x) => {
            // 関数部がラムダ抽象ならβ簡約
            if let Expr::Lambda(param, body) = &**f {
                return Some(substitute(body, param, x));
            }
            // 関数部を先に簡約
            if let Some(new_f) = beta_reduce_once_normal(f) {
                return Some(Expr::App(Box::new(new_f), x.clone()));
            }
            // 引数部を簡約
            if let Some(new_x) = beta_reduce_once_normal(x) {
                return Some(Expr::App(f.clone(), Box::new(new_x)));
            }
            None
        }
        Expr::Lambda(param, body) => {
            beta_reduce_once_normal(body).map(|new_body| Expr::Lambda(param.clone(), Box::new(new_body)))
        }
        _ => None
    }
}

pub fn to_string_expr(expr: &Expr) -> String {
    match expr {
        Expr::Var(v) => v.clone(),
        Expr::Lambda(param, body) => {
            format!("λ{}. {}", param, to_string_expr(body))
        }
        Expr::App(f, x) => {
            format!("({} {})", to_string_expr(f), to_string_expr(x))
        }
    }
}

pub fn format_expression(expr: &str) -> String {
    // 括弧の前後の空白を1つに
    let paren_re = Regex::new(r"\s*([()])\s*").unwrap();
    let formatted = paren_re.replace_all(expr, " $1 ");
    // ラムダ束縛作用素の前後の空白を1つに
    let lambda_re = Regex::new(r"\s*(λ\w+\.\s*)").unwrap();
    let formatted = lambda_re.replace_all(&formatted, " $1 ");
    // 1個以上の空白を1個の空白に置換
    let spaces_re = Regex::new(r"\s+").unwrap();
    let formatted = spaces_re.replace_all(&formatted, " ");
    // 先頭と末尾の空白を削除
    formatted.trim().to_string()
}

pub fn tokenize(lambda: String) -> Vec<String> {
    let re = Regex::new(r"\s+|([()])").unwrap();
    let mut tokens = Vec::new();
    let mut last_end = 0;

    for cap in re.captures_iter(&lambda) {
        if let Some(m) = cap.get(0) {
            if last_end != m.start() {
                tokens.push(lambda[last_end..m.start()].trim().to_string());
            }
            if let Some(paren) = cap.get(1) {
                tokens.push(paren.as_str().to_string());
            }
            last_end = m.end();
        }
    }
    if last_end != lambda.len() {
        tokens.push(lambda[last_end..].trim().to_string());
    }
    tokens.retain(|token| !token.is_empty());
    tokens
}

pub fn to_ast(tokens: Vec<String>) -> Result<Expr, String> {
    let mut index = 0;
    parse_expr_indexed(&tokens, &mut index)
}

fn parse_expr_indexed(tokens: &[String], index: &mut usize) -> Result<Expr, String> {
    parse_application_indexed(tokens, index)
}

fn parse_application_indexed(tokens: &[String], index: &mut usize) -> Result<Expr, String> {
    let mut expr = parse_atom_indexed(tokens, index)?;

    while *index < tokens.len() {
        // 次のトークンが ")" なら停止
        if *index < tokens.len() && tokens[*index] == ")" {
            break;
        }

        let old_index = *index;
        match parse_atom_indexed(tokens, index) {
            Ok(next_expr) => {
                expr = Expr::App(Box::new(expr), Box::new(next_expr));
            },
            Err(_) => {
                *index = old_index; // インデックスを戻す
                break;
            }
        }
    }

    Ok(expr)
}

fn parse_atom_indexed(tokens: &[String], index: &mut usize) -> Result<Expr, String> {
    if *index >= tokens.len() {
        return Err("unexpected end".to_string());
    }

    let token = &tokens[*index];
    *index += 1;

    match token.as_str() {
        "(" => {
            let expr = parse_expr_indexed(tokens, index)?;
            if *index >= tokens.len() || tokens[*index] != ")" {
                return Err("expected )".to_string());
            }
            *index += 1; // consume ")"
            Ok(expr)
        },
        t if t.starts_with("λ") && t.contains('.') => {
            let chars: Vec<char> = t.chars().collect();
            let dot_pos = chars.iter().position(|&c| c == '.').unwrap();
            let param: String = chars[1..dot_pos].iter().collect();
            let body = parse_expr_indexed(tokens, index)?;
            Ok(Expr::Lambda(param, Box::new(body)))
        },
        _ => Ok(Expr::Var(token.clone())),
    }
}

pub fn evaluate_expression(input: String, symbols: &HashMap<String, String>) {
    println!("入力: {}", input);

    // シンボルを展開
    let expanded = expand_symbols(&input, symbols);
    if expanded != input {
        println!("展開: {}", expanded);
    }

    // 式を整形してトークン化
    let formatted = format_expression(&expanded);
    let tokens = tokenize(formatted);

    match to_ast(tokens) {
        Ok(ast) => {
            let reduced;
            let reduced_str;
            if input.contains("step") {
                // 段階的計算を使用
                println!("段階的計算を使用します...");
                reduced = beta_reduce_steps(&ast, 1000); // 最大1000ステップ
                reduced_str = to_string_expr(&reduced);
                println!("段階的結果: {}", reduced_str);
            } else {
                // 通常の完全簡約
                reduced = beta_reduce_full(&ast);
                reduced_str = to_string_expr(&reduced);
                if let Some(n) = is_church_numeral(&reduced) {
                    println!("結果: c{}", n);
                } else {
                    // 式が長すぎる場合は省略
                    if reduced_str.len() > 200 {
                        println!("結果: {}... (長すぎるため省略)", &reduced_str[..200]);
                    } else {
                        println!("結果: {}", reduced_str);
                    }
                }
            }
            let compressed = compress_to_symbols(&reduced_str, symbols);
            if compressed.len() > 200 {
                println!("圧縮: {}... (長すぎるため省略)", &compressed[..200]);
            } else {
                println!("圧縮: {}", compressed);
            }
        },
        Err(e) => {
            println!("エラー: {}", e);
        }
    }
}

pub fn expand_symbols(expr: &str, symbols: &HashMap<String, String>) -> String {
    let mut result = expr.to_string();
    let mut changed = true;

    // Church数c{dec}形式を検出して展開
    let church_re = Regex::new(r"\bc(\d+)\b").unwrap();
    result = church_re.replace_all(&result, |caps: &regex::Captures| {
        let n: usize = caps[1].parse().unwrap_or(0);
        // Church数ラムダ式生成
        let mut body = "z".to_string();
        for _ in 0..n {
            body = format!("s ({})", body);
        }
        format!("(λs.λz.{})", body)
    }).to_string();

    // 再帰的にシンボルを展開（循環参照対策で最大10回まで）
    for _ in 0..10 {
        if !changed { break; }
        changed = false;

        for (symbol, definition) in symbols {
            let pattern = format!(r"\b{}\b", regex::escape(symbol));
            let re = Regex::new(&pattern).unwrap();
            let new_result = re.replace_all(&result, definition).to_string();
            if new_result != result {
                result = new_result;
                changed = true;
            }
        }

        // シンボルの展開で c{n} 形式が導入される可能性があるため
        // ここで再度 Church 数の展開を行う。
        let after_church = church_re.replace_all(&result, |caps: &regex::Captures| {
            let n: usize = caps[1].parse().unwrap_or(0);
            let mut body = "z".to_string();
            for _ in 0..n {
                body = format!("s ({})", body);
            }
            format!("(λs.λz.{})", body)
        }).to_string();
        if after_church != result {
            result = after_church;
            changed = true;
        }
    }

    // 最終的に残った c{n} があれば（定義中に導入されていた場合など）もう一度展開
    result = church_re.replace_all(&result, |caps: &regex::Captures| {
        let n: usize = caps[1].parse().unwrap_or(0);
        let mut body = "z".to_string();
        for _ in 0..n {
            body = format!("s ({})", body);
        }
        format!("(λs.λz.{})", body)
    }).to_string();

    result
}

pub fn compress_to_symbols(expr: &str, symbols: &HashMap<String, String>) -> String {
    let mut result = expr.to_string();

    // AST化した結果
    let formatted = format_expression(&result);
    let ast_result = to_ast(tokenize(formatted.clone())).ok();

    // HashMap定義（symbols）に該当するものはすべて圧縮
    for (symbol, definition) in symbols {
        // 完全一致（括弧除去も考慮）
        if result == *definition {
            return symbol.clone();
        }
        let def_no_parens = definition.trim_start_matches('(').trim_end_matches(')');
        if result == def_no_parens {
            return symbol.clone();
        }
        // AST構造が一致する場合も圧縮
        let def_formatted = format_expression(definition);
        if let (Some(ast_r), Ok(ast_d)) = (ast_result.as_ref(), to_ast(tokenize(def_formatted))) {
            if ast_r == &ast_d {
                return symbol.clone();
            }
        }
    }

    // ASTでChurch数判定（整形してから）
    let formatted = format_expression(&result);
    if let Ok(ast) = to_ast(tokenize(formatted)) {
        if let Some(n) = is_church_numeral(&ast) {
            // HashMap未登録でもc{n}で圧縮
            return format!("c{}", n);
        }
        // true/false判定
        if let Expr::Lambda(t, body) = &ast {
            if let Expr::Lambda(f, body) = &**body {
                // true: λt.λf.t
                if let Expr::Var(v) = &**body {
                    if v == t {
                        return "true".to_string();
                    }
                    if v == f {
                        return "false".to_string();
                    }
                }
            }
        }
        // not true の結果: λf.f
        if let Expr::Lambda(f, body) = &ast {
            if let Expr::Var(v) = &**body {
                if v == f {
                    return "false".to_string();
                }
            }
        }
    }

    // 部分一致（定義が式の一部に含まれる場合も圧縮）
    for (symbol, definition) in symbols {
        let definition_escaped = regex::escape(definition);
        let re = Regex::new(&definition_escaped).unwrap();
        result = re.replace_all(&result, symbol).to_string();
    }

    result
}

pub fn test_simple_cases() {
    println!("=== 単純なケースのテスト ===");

    // (λx.x) y のテスト
    let simple1 = "(λx.x) y".to_string();
    test_expression(simple1);

    // (λx.λy.x) a b のテスト
    let simple2 = "(λx.λy.x) a b".to_string();
    test_expression(simple2);

    // (λt.λf.t) true false のテスト
    let simple3 = "(λt.λf.t) true false".to_string();
    test_expression(simple3);
}

pub fn test_complex_case(symbols: &HashMap<String, String>) {
    println!("\n=== 複雑なケースのテスト（シンボル定義あり） ===");

    // シンボルを使った式
    let lambda = "if (or true false) tt ff".to_string();
    test_expression_with_symbols(lambda, symbols);

    // より複雑な例
    let lambda2 = "if (and true false) success failure".to_string();
    test_expression_with_symbols(lambda2, symbols);

    // not演算子のテスト
    let lambda3 = "not true".to_string();
    test_expression_with_symbols(lambda3, symbols);

    // Church数のテスト
    println!("=== Church数のテスト ===");
    let lambda4 = "succ c2".to_string();
    test_expression_with_symbols(lambda4, symbols);

    let lambda5 = "add c2 c3".to_string();
    test_expression_with_symbols(lambda5, symbols);

    let lambda6 = "mul c2 c3".to_string();
    test_expression_with_symbols(lambda6, symbols);

    let lambda7 = "iszro c0".to_string();
    test_expression_with_symbols(lambda7, symbols);

    let lambda8 = "iszro c1".to_string();
    test_expression_with_symbols(lambda8, symbols);

    let lambda9 = "c3 c4".to_string(); // 4^3 = 64
    test_expression_with_symbols(lambda9, symbols);

    let lambda10 = "c4 c4".to_string(); // 4^4 = 256
    test_expression_with_symbols(lambda10, symbols);

    let lambda11 = "succ(prd c5)".to_string();
    test_expression_with_symbols(lambda11, symbols);

    let lambda12 = "prd(succ c5)".to_string();
    test_expression_with_symbols(lambda12, symbols);
}

fn test_expression_with_symbols(lambda: String, symbols: &HashMap<String, String>) {
    println!("元の式（シンボルあり）: {}", lambda);

    // シンボルを展開
    let expanded = expand_symbols(&lambda, symbols);
    println!("シンボル展開後: {}", expanded);

    // 通常のテストを実行
    let formatted = format_expression(&expanded);

    let tokens = tokenize(formatted.clone());

    match to_ast(tokens) {
        Ok(ast) => {
            let reduced = beta_reduce_full(&ast);
            let reduced_str = to_string_expr(&reduced);

            // 簡約結果をシンボルに再変換
            let compressed = compress_to_symbols(&reduced_str, symbols);

            println!("β簡約結果: {}", reduced_str);
            if compressed != reduced_str {
                println!("シンボル圧縮後: {}", compressed);
            }
        },
        Err(e) => {
            println!("パースエラー: {}", e);
        }
    }
    println!();
}

fn test_expression(lambda: String) {
    let formatted = format_expression(&lambda);
    println!("元の式: {}", lambda);
    println!("整形: {}", formatted);
    let tokens = tokenize(formatted.clone());
    println!("トークン: {:?}", tokens);

    match to_ast(tokens) {
        Ok(ast) => {
            println!("AST: {:?}", ast);
            let reduced = beta_reduce_full(&ast);
            println!("β簡約結果: {:?}", reduced);
            println!("β簡約結果(文字列): {}", to_string_expr(&reduced));
        },
        Err(e) => {
            println!("パースエラー: {}", e);
        }
    }
    println!();
}
