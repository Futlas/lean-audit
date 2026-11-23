use regex::Regex;
use std::collections::HashMap;

pub fn split_lean_ident(raw: &str) -> Vec<String> {
    let tail = raw.rsplit('.').next().unwrap_or(raw).trim_matches('\'');
    let mut words = Vec::new();
    let mut cur = String::new();
    let chars: Vec<char> = tail.chars().collect();

    for i in 0..chars.len() {
        let ch = chars[i];
        if ch == '_' || ch == '-' || ch == ' ' {
            if !cur.is_empty() {
                words.push(cur.to_lowercase());
                cur.clear();
            }
            continue;
        }
        if ch.is_uppercase() && !cur.is_empty() {
            let prev_lower = chars[i - 1].is_lowercase();
            let next_lower = i + 1 < chars.len() && chars[i + 1].is_lowercase();
            if prev_lower || next_lower {
                words.push(cur.to_lowercase());
                cur.clear();
            }
        }
        cur.push(ch);
    }
    if !cur.is_empty() {
        words.push(cur.to_lowercase());
    }

    // Дополнительно разрезаем частые слепленные префиксы/суффиксы в нижнем регистре
    let mut expanded = Vec::new();
    for w in words {
        if w == "rhofall" {
            expanded.extend(["rh", "of", "all"].into_iter().map(String::from));
        } else if w == "allchi" {
            expanded.extend(["all", "chi"].into_iter().map(String::from));
        } else if w == "everycharacter" {
            expanded.extend(["every", "character"].into_iter().map(String::from));
        } else {
            expanded.push(w);
        }
    }
    expanded
}

fn term_dict() -> HashMap<&'static str, &'static str> {
    HashMap::from([
        ("rh", "Riemann Hypothesis"),
        ("riemannhypothesis", "Riemann Hypothesis"),
        ("eq", "equality"),
        ("ne", "non-vanishing"),
        ("nonvanishing", "non-vanishing"),
        ("cusp", "cuspidal"),
        ("cuspex", "cuspidal existence"),
        ("artex", "Arthur parameter existence"),
        ("eis", "Eisenstein series"),
        ("gl", "$\\mathrm{GL}_n$"),
        ("wd", "Weil--Deligne"),
        ("vwin", "vertical window"),
        ("rect", "recursive parameter"),
        ("rectexists", "existence of recursive parameter"),
        ("recnotion", "recursive Langlands parameter structure"),
        ("cos", "standard cosocle"),
        ("cosocle", "standard cosocle"),
        ("standardcosoclegl", "standard cosocle for $\\mathrm{GL}_n$"),
        ("chi", "Dirichlet character $\\chi$"),
        ("lfunction", "$L$-function"),
        ("zeta", "Riemann zeta function"),
        ("dim", "dimension"),
        ("pushdown", "push-down"),
        ("heightbounds", "height bounds"),
        ("unif", "uniform"),
        ("int", "integral"),
        ("reg", "regularity"),
        ("galois", "Galois"),
        ("theta", "theta correspondence"),
        ("lift", "functorial lift"),
        ("tliftk", "twisted lift at level $k$"),
        ("seg", "segment"),
        ("row0b", "row condition $(0\\mathrm{b})$"),
        ("holds", "holds"),
        ("exists", "existence"),
        ("lext", "$L$-extension"),
        ("islext", "existence of $L$-extension"),
        ("geoone", "geometric base case"),
        ("htriv", "trivial hypothesis"),
    ])
}

pub fn humanize_title(raw_ident: &str) -> String {
    let dict = term_dict();
    let words = split_lean_ident(raw_ident);
    if words.is_empty() {
        return raw_ident.to_string();
    }

    let mut out: Vec<String> = Vec::new();
    for (idx, w) in words.iter().enumerate() {
        let mapped = if w == "of" {
            match words.get(idx + 1).map(|s| s.as_str()) {
                Some("all" | "every") => "for",
                _ => "from",
            }
        } else {
            dict.get(w.as_str()).copied().unwrap_or(w.as_str())
        };
        if out.last().map(|prev| prev.to_lowercase()) != Some(mapped.to_lowercase()) {
            out.push(mapped.to_string());
        }
    }

    let mut phrase = out.join(" ");
    if let Some(first) = phrase.get_mut(0..1) {
        first.make_ascii_uppercase();
    }
    phrase
}

/// Заменяет длинные CamelCase/snake_case идентификаторы внутри математических выражений
/// Выходит из режима `$ ... $` для многословных фраз, чтобы LaTeX свободно переносил строки!
pub fn humanize_math_expr(expr: &str) -> String {
    let dict = term_dict();
    let ident_re = Regex::new(r"\b[A-Za-z][A-Za-z0-9_']{3,}\b").unwrap();
    ident_re
        .replace_all(expr, |caps: &regex::Captures| {
            let tok = caps.get(0).unwrap().as_str();
            let low = tok.to_lowercase();
            if let Some(&mapped) = dict.get(low.as_str()) {
                format!("$\\textrm{{{}}} $", mapped.replace('$', ""))
            } else if tok.contains('_') || tok.chars().filter(|c| c.is_uppercase()).count() >= 2 {
                let words = split_lean_ident(tok);
                format!("$\\textrm{{{}}} $", words.join(" "))
            } else {
                tok.to_string()
            }
        })
        .to_string()
}

pub fn compose_math_prose(hyps: &[String], goal: &str, is_def: bool) -> String {
    let g = humanize_math_expr(goal);
    if is_def {
        if hyps.is_empty() {
            return format!("We define this notion by the condition ${g}$.");
        }
        let hs: Vec<String> = hyps.iter().map(|h| humanize_math_expr(h)).collect();
        return format!(
            "For parameters ${}$, this structure is characterized by ${g}$.",
            hs.join("$, $")
        ).replace("$$", "").replace("$ $", " ");
    }
    if hyps.is_empty() {
        format!("We establish that ${g}$ holds.")
    } else if hyps.len() == 1 {
        let h0 = humanize_math_expr(&hyps[0]);
        format!("Assuming ${h0}$, it follows that ${g}$.")
    } else {
        let hs: Vec<String> = hyps.iter().map(|h| humanize_math_expr(h)).collect();
        let last = hs.last().unwrap();
        let init = &hs[..hs.len() - 1];
        format!(
            "Under the hypotheses ${}$ and ${last}$, we establish that ${g}$.",
            init.join("$, $")
        )
    }
}
