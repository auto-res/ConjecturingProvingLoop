

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro hP2
  intro x hxA
  have hx' : x ∈ interior (closure (interior A)) := hP2 hxA
  exact interior_subset hx'

theorem P2_implies_P3 {A : Set X} : P2 A → P3 A := by
  intro hP2
  intro x hxA
  have hx1 : x ∈ interior (closure (interior A)) := hP2 hxA
  have hsubset : closure (interior A) ⊆ closure A := closure_mono interior_subset
  exact (interior_mono hsubset) hx1

theorem P3_of_dense {A : Set X} (hA : closure A = Set.univ) : P3 A := by
  intro x hx
  simpa [hA, interior_univ]

theorem P3_of_open {A : Set X} (hA : IsOpen A) : P3 A := by
  intro x hx
  have h_mem_nhds : (closure A : Set X) ∈ 𝓝 x := by
    have hA_nhds : (A : Set X) ∈ 𝓝 x := hA.mem_nhds hx
    exact
      Filter.mem_of_superset hA_nhds
        (subset_closure : (A : Set X) ⊆ closure A)
  exact (mem_interior_iff_mem_nhds).2 h_mem_nhds

theorem P2_union {A B : Set X} : P2 A → P2 B → P2 (A ∪ B) := by
  intro hP2A hP2B
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hx1 : x ∈ interior (closure (interior A)) := hP2A hxA
      -- `closure (interior A)` is contained in `closure (interior (A ∪ B))`
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact (interior_mono hsubset) hx1
  | inr hxB =>
      -- `x ∈ B`
      have hx1 : x ∈ interior (closure (interior B)) := hP2B hxB
      -- `closure (interior B)` is contained in `closure (interior (A ∪ B))`
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact (interior_mono hsubset) hx1