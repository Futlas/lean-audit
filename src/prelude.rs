use std::collections::HashSet;

/// Генерирует универсальный StandalonePrelude.lean для автономной компиляции срезов без Mathlib
pub fn build_standalone_prelude(extra_symbols: &HashSet<String>) -> String {
    let mut out = String::from(
        r#"module
public section
noncomputable section
axiom RealType : Type
axiom RatType : Type
structure ComplexType where
  re : RealType
  im : RealType

notation "ℕ" => Nat
notation "ℤ" => Int
notation "ℚ" => RatType
notation "ℝ" => RealType
notation "ℂ" => ComplexType

axiom zeroR : ℝ
axiom oneR : ℝ
axiom twoR : ℝ
axiom zeroQ : ℚ
axiom oneQ : ℚ
axiom zeroC : ℂ
axiom oneC : ℂ
axiom natToC : ℕ → ℂ
axiom natToR : ℕ → ℝ
axiom intToC : ℤ → ℂ
axiom hmulICC : Int → ℂ → ℂ
axiom divR : ℝ → ℝ → ℝ
axiom ltR : ℝ → ℝ → Prop
axiom leR : ℝ → ℝ → Prop

instance : OfNat ℝ 0 := ⟨zeroR⟩
instance : OfNat ℝ 1 := ⟨oneR⟩
instance : OfNat ℝ 2 := ⟨twoR⟩
instance : OfNat ℚ 0 := ⟨zeroQ⟩
instance : OfNat ℚ 1 := ⟨oneQ⟩
instance : OfNat ℂ 0 := ⟨zeroC⟩
instance : OfNat ℂ 1 := ⟨oneC⟩
instance : Coe ℕ ℂ := ⟨natToC⟩
instance : Coe ℕ ℝ := ⟨natToR⟩
instance : Coe ℤ ℂ := ⟨intToC⟩
axiom haddCN : ℂ → ℕ → ℂ
axiom haddCC : ℂ → ℂ → ℂ
instance : HMul Int ℂ ℂ := ⟨hmulICC⟩
instance : HAdd ℂ ℕ ℂ := ⟨haddCN⟩
instance : HAdd ℂ ℂ ℂ := ⟨haddCC⟩
instance : Div ℝ := ⟨divR⟩
instance : LT ℝ := ⟨ltR⟩
instance : LE ℝ := ⟨leR⟩

axiom riemannZeta : ℂ → ℂ
def RiemannHypothesis : Prop := ∀ s : ℂ, riemannZeta s = 0 → s.re = (1 / 2 : ℝ)

axiom DirichletCharacter : Type → Nat → Type
namespace DirichletCharacter
axiom IsPrimitive {R : Type} {N : Nat} : DirichletCharacter R N → Prop
axiom LFunction {N : Nat} : DirichletCharacter ℂ N → ℂ → ℂ
axiom completedLFunction {N : Nat} : DirichletCharacter ℂ N → ℂ → ℂ
axiom gammaFactor {N : Nat} : DirichletCharacter ℂ N → ℂ → ℂ
end DirichletCharacter

axiom oneChi {N : ℕ} : DirichletCharacter ℂ N
instance {N : ℕ} : OfNat (DirichletCharacter ℂ N) 1 := ⟨oneChi⟩
"#,
    );

    // Автоматически объявляем внешние типы/константы, обнаруженные в срезе
    let builtin_skip: HashSet<&str> = [
        "Nat", "Int", "Bool", "Prop", "Type", "Sort", "Unit", "True", "False",
        "And", "Or", "Not", "Eq", "Ne", "Exists", "Sigma", "Subtype", "List", "Array",
        "Option", "String", "Char", "Float", "UInt8", "UInt16", "UInt32", "UInt64", "USize",
        "RealType", "RatType", "ComplexType", "RiemannHypothesis", "DirichletCharacter",
        "riemannZeta", "Classical", "NeZero", "Fact", "OfNat", "Coe", "HMul", "Div", "LT", "LE",
    ]
    .into_iter()
    .collect();

    let mut sorted: Vec<&String> = extra_symbols.iter().collect();
    sorted.sort();
    for sym in sorted {
        if builtin_skip.contains(sym.as_str()) || sym.contains('.') {
            continue;
        }
        out.push_str(&format!("axiom {sym} {{α : Sort _}} : α\n"));
    }

    out.push_str("end\nend\n");
    out
}
