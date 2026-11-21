-- 1. Ловушка «принципа взрыва»: противоречивые гипотезы (x < 3 и 5 < x)
theorem fake_riemann_bug (x : Nat) (h1 : x < 3) (h2 : 5 < x) : x = 100 := by
  omega

-- 2. «Потёмкинская» гипотеза: условие h_unused вообще не нужно для доказательства
theorem unused_hyp_bug (a b : Nat) (h_unused : a = 42) : a + b = b + a := by
  exact Nat.add_comm a b
