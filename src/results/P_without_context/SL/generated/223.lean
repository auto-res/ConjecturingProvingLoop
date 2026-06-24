

theorem P2_imp_P3 {A : Set X} : P2 A → P3 A :=
by
  intro hP2
  intro x
  intro hxA
  have hx_in : x ∈ interior (closure (interior A)) := hP2 hxA
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact hsubset hx_in