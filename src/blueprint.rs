use crate::core::{build_dag, ProofDag};
use regex::Regex;
use std::collections::{HashSet, VecDeque};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

#[derive(Clone)]
struct DeclItem {
    kind: String,
    title: String,
    doc: Option<String>,
    hyps: Vec<String>,
    goal: String,
    proof_sketch: Option<String>,
}

#[derive(Clone)]
struct Chapter {
    name: String,
    items: Vec<DeclItem>,
}

struct Part {
    title: String,
    intro: String,
    chapters: Vec<Chapter>,
}

fn clean_binders(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut depth = 0usize;
    for ch in s.chars() {
        match ch {
            '[' => depth += 1,
            ']' => depth = depth.saturating_sub(1),
            _ if depth == 0 => out.push(ch),
            _ => {}
        }
    }
    let ns_re = Regex::new(r"(?:_root_\.)?(?:[A-Z][A-Za-z0-9_']*\.)+([A-Za-z0-9_']+)").unwrap();
    let no_ns = ns_re.replace_all(&out, "$1");
    no_ns.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn humanize(raw: &str) -> String {
    let base = raw.rsplit('.').next().unwrap_or(raw).replace('_', " ");
    let trimmed = base
        .trim_end_matches(" of open")
        .trim_end_matches(" of via")
        .trim_end_matches(" of")
        .trim();
    let mut c = trimmed.chars();
    match c.next() {
        None => String::new(),
        Some(f) => f.to_uppercase().collect::<String>() + c.as_str(),
    }
}

fn split_sig(sig: &str) -> (Vec<String>, String) {
    let (mut dp, mut db, mut dc) = (0usize, 0usize, 0usize);
    let mut colon = None;
    for (i, ch) in sig.char_indices() {
        match ch {
            '(' => dp += 1,
            ')' => dp = dp.saturating_sub(1),
            '[' => db += 1,
            ']' => db = db.saturating_sub(1),
            '{' => dc += 1,
            '}' => dc = dc.saturating_sub(1),
            ':' if dp == 0 && db == 0 && dc == 0 => {
                colon = Some(i);
                break;
            }
            _ => {}
        }
    }
    let Some(pos) = colon else {
        return (Vec::new(), sig.trim().to_string());
    };
    let mut hyps = Vec::new();
    let mut start = None;
    let mut d = 0usize;
    for (i, ch) in sig[..pos].char_indices() {
        match ch {
            '(' => {
                if d == 0 { start = Some(i + 1); }
                d += 1;
            }
            ')' => {
                d = d.saturating_sub(1);
                if d == 0 {
                    if let Some(st) = start.take() {
                        let inner = sig[st..i].trim();
                        if !inner.is_empty() { hyps.push(inner.to_string()); }
                    }
                }
            }
            _ => {}
        }
    }
    (hyps, sig[pos + 1..].trim().to_string())
}

fn extract_subgoals(body: &str) -> Vec<String> {
    let have_re = Regex::new(r"(?m)^\s*have\s+[A-Za-z0-9_']*\s*:\s*([^:=\n]+)\s*:=").unwrap();
    let mut goals = Vec::new();
    for cap in have_re.captures_iter(body) {
        let raw_g = clean_binders(cap.get(1).unwrap().as_str().trim());
        if raw_g.len() >= 4 && raw_g.len() <= 140 && !goals.contains(&raw_g) {
            goals.push(raw_g);
        }
        if goals.len() >= 3 { break; }
    }
    goals
}

fn extract_theorem_calls(text: &str) -> Vec<String> {
    let id_re = Regex::new(r"\b([A-Za-z][A-Za-z0-9_.']{3,})\b").unwrap();
    let local_hyp_re = Regex::new(r"^h[A-Z0-9_]").unwrap();
    let skip = [
        "fun", "let", "in", "match", "with", "if", "then", "else", "have", "show", "from",
        "exact", "apply", "refine", "rw", "simp", "omega", "linarith", "nlinarith", "norm_num",
        "decide", "ring", "field_simp", "induction", "cases", "rcases", "obtain", "by_contra",
        "contradiction", "intro", "intros", "constructor", "ext", "aesop", "rfl", "trivial",
        "this", "done", "sorry", "true", "false", "And", "Or", "Not", "Nat", "Int", "Real",
        "Complex", "Prop", "Type", "Sort", "UpperTheory", "Development", "Formalism",
        "GlobalTheory", "GroundTheory", "ReciprocityTheory", "CompanionTheory",
    ];
    let mut refs = Vec::new();
    for cap in id_re.captures_iter(text) {
        let raw = cap.get(1).unwrap().as_str();
        let short = raw.rsplit('.').next().unwrap_or(raw);
        if short.len() <= 3 || skip.contains(&short) || local_hyp_re.is_match(short) {
            continue;
        }
        let readable = short.replace('_', " ");
        if !refs.contains(&readable) { refs.push(readable); }
        if refs.len() >= 4 { break; }
    }
    refs
}

fn summarize_proof(body: &str) -> Option<String> {
    let trimmed = body.trim();
    if trimmed.is_empty() { return None; }

    let subgoals = extract_subgoals(trimmed);
    let refs = extract_theorem_calls(trimmed);

    if !trimmed.starts_with("by") && trimmed.len() < 120 {
        return if refs.is_empty() {
            Some("Direct consequence of the preceding definitions.".to_string())
        } else {
            Some(format!("Follows directly from \\texttt{{{}}}.", tex_escape(&refs.join(", "))))
        };
    }

    if !trimmed.starts_with("by") {
        let mut msg = String::from("Constructed by combining intermediate reductions");
        if !refs.is_empty() {
            msg.push_str(&format!(", specifically \\texttt{{{}}}", tex_escape(&refs.join(", "))));
        }
        msg.push('.');
        return Some(msg);
    }

    let tactic_body = trimmed.trim_start_matches("by").trim();
    let mut methods = Vec::new();
    if tactic_body.contains("induction ") { methods.push("mathematical induction"); }
    if tactic_body.contains("by_contra") || tactic_body.contains("contradiction") || tactic_body.contains("lt_irrefl") {
        methods.push("contradiction");
    }
    if tactic_body.contains("cases ") || tactic_body.contains("rcases ") || tactic_body.contains("obtain ") {
        methods.push("case decomposition");
    }
    if tactic_body.contains("omega") || tactic_body.contains("linarith") || tactic_body.contains("nlinarith") {
        methods.push("linear and nonlinear arithmetic bounds");
    }
    if tactic_body.contains("norm_num") || tactic_body.contains("decide") {
        methods.push("explicit numerical verification");
    }
    if tactic_body.contains("ring") || tactic_body.contains("field_simp") || tactic_body.contains("simp") || tactic_body.contains("rw [") {
        methods.push("algebraic rewriting");
    }

    let mut sentences = Vec::new();
    if !subgoals.is_empty() {
        let math_goals: Vec<String> = subgoals.iter().map(|g| format!("${}$", to_latex_math(g))).collect();
        sentences.push(format!("First, we establish the intermediate claims {}.", math_goals.join(" and ")));
    }
    let concl = match (methods.is_empty(), refs.is_empty()) {
        (false, false) => format!("The proof proceeds via {}, invoking \\texttt{{{}}}.", methods.join(", "), tex_escape(&refs.join(", "))),
        (false, true) => format!("The claim follows via {}.", methods.join(", ")),
        (true, false) => format!("The proof concludes by applying \\texttt{{{}}}.", tex_escape(&refs.join(", "))),
        (true, true) => "The claim follows directly from the structural hypotheses.".to_string(),
    };
    sentences.push(concl);
    Some(sentences.join(" "))
}

fn to_latex_math(s: &str) -> String {
    let frac_re = Regex::new(r"\b(\d+)\s*/\s*(\d+)\b").unwrap();
    let pow_re = Regex::new(r"([A-Za-z0-9_]+)\s*\^\s*([A-Za-z0-9_]+)").unwrap();
    let set_re = Regex::new(r"\b([A-Za-z0-9_']+)\s*:\s*(ℕ|ℤ|ℚ|ℝ|ℂ)\b").unwrap();
    let word_re = Regex::new(r"(^|[^\\A-Za-z])([A-Za-z][A-Za-z0-9_]{1,})").unwrap();

    let mut out = set_re.replace_all(s, "$1 \\in $2").to_string();
    for (a, b) in [
        ("∀", r"\forall "), ("∃", r"\exists "), ("→", r"\to "), ("->", r"\to "),
        ("↔", r"\iff "), ("<->", r"\iff "), ("≤", r"\le "), ("<=", r"\le "),
        ("≥", r"\ge "), (">=", r"\ge "), ("≠", r"\neq "), ("!=", r"\neq "),
        ("∧", r"\land "), ("∨", r"\lor "), ("¬", r"\neg "), ("∈", r"\in "),
        ("∉", r"\notin "), ("⊆", r"\subseteq "), ("∪", r"\cup "), ("∩", r"\cap "),
        ("∅", r"\emptyset "), ("ℝ", r"\mathbb{R}"), ("ℂ", r"\mathbb{C}"),
        ("ℚ", r"\mathbb{Q}"), ("ℕ", r"\mathbb{N}"), ("ℤ", r"\mathbb{Z}"),
        ("𝓞", r"\mathcal{O}"), ("𝒪", r"\mathcal{O}"), ("𝔭", r"\mathfrak{p}"),
        ("𝔮", r"\mathfrak{q}"), ("𝔄", r"\mathfrak{A}"), ("𝔪", r"\mathfrak{m}"),
        ("α", r"\alpha "), ("β", r"\beta "), ("γ", r"\gamma "), ("δ", r"\delta "),
        ("ε", r"\varepsilon "), ("ζ", r"\zeta "), ("η", r"\eta "), ("θ", r"\theta "),
        ("λ", r"\lambda "), ("μ", r"\mu "), ("ν", r"\nu "), ("π", r"\pi "),
        ("ρ", r"\rho "), ("σ", r"\sigma "), ("τ", r"\tau "), ("φ", r"\varphi "),
        ("χ", r"\chi "), ("ψ", r"\psi "), ("ω", r"\omega "), ("Γ", r"\Gamma "),
        ("Δ", r"\Delta "), ("Λ", r"\Lambda "), ("Π", r"\Pi "), ("Σ", r"\Sigma "),
        ("Φ", r"\Phi "), ("Ψ", r"\Psi "), ("Ω", r"\Omega "), ("∑", r"\sum "),
        ("∏", r"\prod "), ("∫", r"\int "), ("∞", r"\infty "), ("×", r"\times "),
        ("⊗", r"\otimes "), ("⊕", r"\oplus "), ("∘", r"\circ "), ("·", r"\cdot "),
        ("⟨", r"\langle "), ("⟩", r"\rangle "), ("‖", r"\|"), ("∣", r"\mid "),
    ] {
        out = out.replace(a, b);
    }
    out = frac_re.replace_all(&out, r"\frac{$1}{$2}").to_string();
    out = pow_re.replace_all(&out, r"{$1}^{$2}").to_string();
    out = word_re
        .replace_all(&out, |caps: &regex::Captures| {
            let prefix = caps.get(1).unwrap().as_str();
            let word = caps.get(2).unwrap().as_str().replace('_', r"\_");
            format!("{prefix}\\mathrm{{{word}}}")
        })
        .to_string();
    out = out.replace('%', r"\%").replace('#', r"\#").replace('&', r"\&");
    let out = out.split("--").next().unwrap_or(&out).to_string();
    let out = out.split("--").next().unwrap_or(&out).to_string();
    let ascii_only: String = out.chars().map(|c| if c.is_ascii() { c } else { '?' }).collect();
    ascii_only.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn tex_escape(s: &str) -> String {
    s.replace('\\', r"\textbackslash{}")
        .replace('_', r"\_").replace('&', r"\&").replace('%', r"\%")
        .replace('$', r"\$").replace('#', r"\#").replace('{', r"\{").replace('}', r"\}")
}

fn parse_file(content: &str, only_theorems: bool, include_props: bool, used_symbols: Option<&HashSet<String>>) -> Vec<DeclItem> {
    let re = Regex::new(
        r"^(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|structure|def|inductive)\s+([A-Za-z0-9_.']+)",
    ).unwrap();
    let lines: Vec<&str> = content.lines().collect();
    let mut out = Vec::new();

    for (idx, line) in lines.iter().enumerate() {
        let Some(cap) = re.captures(line.trim_start()) else { continue };
        let kind = cap.get(1).unwrap().as_str().to_string();
        if only_theorems && kind != "theorem" && kind != "lemma" { continue; }
        let name = cap.get(2).unwrap().as_str();
        if let Some(used) = used_symbols {
            let short_name = name.rsplit('.').next().unwrap_or(name);
            if !used.contains(short_name) { continue; }
        }

        let mut doc = None;
        let mut i = idx;
        while i > 0 {
            let prev = lines[i - 1].trim();
            if prev.is_empty() || prev.starts_with("@[") { i -= 1; continue; }
            if prev.ends_with("-/") {
                let mut buf = Vec::new();
                let mut j = i - 1;
                loop {
                    let l = lines[j].trim();
                    let c = l.trim_start_matches("/--").trim_start_matches("/*")
                        .trim_end_matches("-/").trim_start_matches('*').trim();
                    if !c.is_empty() { buf.push(c.to_string()); }
                    if l.starts_with("/--") || j == 0 { break; }
                    j -= 1;
                }
                buf.reverse();
                if !buf.is_empty() { doc = Some(buf.join(" ")); }
            }
            break;
        }

        let mut raw_sig = String::new();
        let mut body = String::new();
        let mut in_body = false;
        for l in lines.iter().skip(idx).take(45) {
            let t = l.trim();
            if !in_body {
                if t.is_empty() { break; }
                if let Some(p) = t.find(":=") {
                    raw_sig.push_str(t[..p].trim());
                    in_body = true;
                    body.push_str(t[p + 2..].trim());
                    body.push('\n');
                } else if t.ends_with(" where") || t == "where" {
                    raw_sig.push_str(t.trim_end_matches("where").trim());
                    break;
                } else {
                    if !raw_sig.is_empty() { raw_sig.push(' '); }
                    raw_sig.push_str(t);
                }
            } else {
                if t.starts_with("theorem ") || t.starts_with("lemma ") || t.starts_with("def ")
                    || t.starts_with("structure ") || t.starts_with("end ") { break; }
                body.push_str(t);
                body.push('\n');
            }
        }

        let after = raw_sig.find(name).map(|p| &raw_sig[p + name.len()..]).unwrap_or("");
        let (hyps, mut goal) = split_sig(&clean_binders(after));
        if kind == "def" && goal == "Prop" {
            let clean_body = clean_binders(body.trim());
            if clean_body.is_empty() && !include_props && doc.is_none() { continue; }
            if !clean_body.is_empty() && clean_body.len() <= 260 { goal = clean_body; }
            else if !include_props && doc.is_none() { continue; }
        }
        let proof_sketch = if kind == "theorem" || kind == "lemma" { summarize_proof(&body) } else { None };
        out.push(DeclItem { kind, title: humanize(name), doc, hyps, goal, proof_sketch });
    }
    out
}

pub fn run_blueprint(
    src_dir: &Path,
    entry: &str,
    max_depth: usize,
    only_theorems: bool,
    include_props: bool,
    tex_path: PathBuf,
    md_out: Option<PathBuf>,
    tree_shake: bool,
) -> ExitCode {
    let used_symbols = if tree_shake {
        if let Ok(dag) = ProofDag::build(src_dir, entry, None) {
            dag.collect_used_symbols(dag.layers.len(), &[])
        } else {
            HashSet::new()
        }
    } else {
        HashSet::new()
    };
    let sym_filter = if tree_shake { Some(&used_symbols) } else { None };

    let (_, nodes) = build_dag(src_dir);
    if !nodes.contains_key(entry) {
        eprintln!("Error: entry module `{entry}` not found in {:?}", src_dir);
        return ExitCode::from(2);
    }

    let mut visited = HashSet::new();
    let mut seen_hashes = HashSet::new();
    let mut queue = VecDeque::new();
    let mut by_depth: Vec<Vec<Chapter>> = vec![Vec::new(); max_depth + 1];
    let mut total_modules = 0usize;

    visited.insert(entry.to_string());
    queue.push_back((entry.to_string(), 0usize));

    while let Some((curr, depth)) = queue.pop_front() {
        if depth > max_depth { continue; }
        let Some(node) = nodes.get(&curr) else { continue };
        if !seen_hashes.insert(node.content_hash) { continue; }
        total_modules += 1;

        let content = fs::read_to_string(&node.path).unwrap_or_default();
        let items = parse_file(&content, only_theorems, include_props, sym_filter);
        if !items.is_empty() {
            by_depth[depth].push(Chapter { name: humanize(&node.name), items });
        }
        for imp in &node.imports {
            if nodes.contains_key(imp) && visited.insert(imp.clone()) {
                queue.push_back((imp.clone(), depth + 1));
            }
        }
    }

    let mut parts = Vec::new();
    for (lvl, chapters) in by_depth.into_iter().enumerate() {
        if chapters.is_empty() { continue; }
        let (title, intro) = match lvl {
            0 => ("Main Results".to_string(), format!("Primary theorems established at the top level of {entry}.")),
            1 => ("Primary Reductions".to_string(), "Intermediate reductions supporting the main statements.".to_string()),
            _ => (format!("Supporting Lemmas and Definitions (Depth {lvl})"), format!("Auxiliary statements and structures at depth {lvl}.")),
        };
        parts.push(Part { title, intro, chapters });
    }

    let total_items: usize = parts.iter().flat_map(|p| &p.chapters).map(|c| c.items.len()).sum();
    let mut tex = String::from(
        "\\documentclass[11pt,a4paper]{article}\n\\usepackage[utf8]{inputenc}\n\\usepackage[T1]{fontenc}\n\\usepackage{lmodern}\n\\usepackage{amsmath,amssymb,amsthm}\n\\usepackage[margin=2.6cm]{geometry}\n\\usepackage{microtype}\n\\usepackage[colorlinks=true,linkcolor=blue!55!black]{hyperref}\n\\linespread{1.2}\n\\emergencystretch=3em\n\\newtheoremstyle{cleanthm}{10pt}{10pt}{\\itshape}{}{\\bfseries}{.}{0.6em}{}\n\\newtheoremstyle{cleandef}{10pt}{10pt}{\\normalfont}{}{\\bfseries}{.}{0.6em}{}\n\\theoremstyle{cleanthm}\n\\newtheorem{theorem}{Theorem}[subsection]\n\\newtheorem{lemma}[theorem]{Lemma}\n\\theoremstyle{cleandef}\n\\newtheorem{definition}[theorem]{Definition}\n\n",
    );
    tex.push_str(&format!("\\title{{\\textbf{{Architectural Proof Outline: {}}}}}\n\\author{{Extracted automatically by \\texttt{{lean-audit}}}}\n\\date{{\\today}}\n\n\\begin{{document}}\n\\maketitle\n\n", tex_escape(&humanize(entry))));
    tex.push_str(&format!("\\begin{{abstract}}\nFormal dependency outline rooted at \\texttt{{{}}}, covering {} layers ({} deduplicated modules, {} statements).\n\\end{{abstract}}\n\n\\tableofcontents\n\\vspace{{1.5em}}\n\n", tex_escape(entry), parts.len(), total_modules, total_items));

    for p in &parts {
        tex.push_str(&format!("\\section{{{}}}\n{}\n\n", tex_escape(&p.title), tex_escape(&p.intro)));
        for ch in &p.chapters {
            tex.push_str(&format!("\\subsection{{{}}}\n", tex_escape(&ch.name)));
            for it in &ch.items {
                let env = match it.kind.as_str() { "theorem" => "theorem", "lemma" => "lemma", _ => "definition" };
                tex.push_str(&format!("\\begin{{{env}}}[{}]\n", tex_escape(&it.title)));
                if let Some(ref d) = it.doc { tex.push_str(&format!("{}\n\n", tex_escape(d))); }
                if !it.hyps.is_empty() {
                    let hs = it.hyps.iter().map(|h| format!("${}$", to_latex_math(h))).collect::<Vec<_>>().join(", ");
                    tex.push_str(&format!("Suppose that {hs}. "));
                }
                if !it.goal.is_empty() {
                    if it.goal.len() > 260 {
                        tex.push_str("Then the compound structural condition holds (see formal source).\n");
                    } else {
                        tex.push_str(&format!("Then ${}$.\n", to_latex_math(&it.goal)));
                    }
                }
                tex.push_str(&format!("\\end{{{env}}}\n"));
                if let Some(ref sketch) = it.proof_sketch {
                    tex.push_str(&format!("\\begin{{proof}}\n{sketch}\n\\end{{proof}}\n"));
                }
                tex.push('\n');
            }
        }
    }
    tex.push_str("\\end{document}\n");

    if let Err(e) = fs::write(&tex_path, &tex) {
        eprintln!("Failed to write LaTeX file: {e}");
        return ExitCode::from(2);
    }
    println!("LaTeX proof outline saved to: {:?}", tex_path);

    if let Some(md_path) = md_out {
        let _ = fs::write(&md_path, format!("# Proof Outline: {entry}\n\nGenerated {total_items} items across {total_modules} modules.\n"));
    }
    ExitCode::SUCCESS
}
