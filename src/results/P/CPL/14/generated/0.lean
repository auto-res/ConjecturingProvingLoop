

theorem P3_of_P2 {X} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro hP2
  have hsubset : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  have hmono : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono hsubset
  exact hP2.trans hmono

theorem P1_open {X} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A := by
  intro x hx
  have h_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  exact subset_closure h_int

theorem P2_univ {X} [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  intro x hx
  simp [interior_univ, closure_univ] at *

theorem P3_iff_forall_point {X} [TopologicalSpace X] {A : Set X} : P3 A ↔ ∀ x, x ∈ A → ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure A := by
  constructor
  · intro hP3 x hxA
    have hx_int : x ∈ interior (closure A) := hP3 hxA
    exact ⟨interior (closure A), isOpen_interior, hx_int, interior_subset⟩
  · intro h x hxA
    rcases h x hxA with ⟨U, hUopen, hxU, hUsubset⟩
    have h_closure_nhds : (closure A : Set X) ∈ 𝓝 x := by
      have hU_nhds : (U : Set X) ∈ 𝓝 x := hUopen.mem_nhds hxU
      exact Filter.mem_of_superset hU_nhds hUsubset
    exact (mem_interior_iff_mem_nhds).2 h_closure_nhds