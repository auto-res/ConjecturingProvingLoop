

theorem open_set_has_P1 {A : Set X} (hA : IsOpen A) : P1 A := by
  intro x hx
  have hIA : interior A = A := hA.interior_eq
  have : x ∈ closure A := subset_closure hx
  simpa [hIA] using this

theorem P2_implies_P3 {A : Set X} (hA : P2 A) : P3 A := by
  intro x hx
  exact (interior_mono (closure_mono interior_subset)) (hA hx)

theorem union_P1 {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA' =>
      -- `x` comes from `A`
      have hx_cl : x ∈ closure (interior A) := hA hA'
      -- `interior A` is contained in `interior (A ∪ B)`
      have hsubset : interior A ⊆ interior (A ∪ B) := by
        have hAB : (A : Set X) ⊆ A ∪ B := by
          intro z hz
          exact Or.inl hz
        exact interior_mono hAB
      -- enlarge the closure
      exact (closure_mono hsubset) hx_cl
  | inr hB' =>
      -- `x` comes from `B`
      have hx_cl : x ∈ closure (interior B) := hB hB'
      -- `interior B` is contained in `interior (A ∪ B)`
      have hsubset : interior B ⊆ interior (A ∪ B) := by
        have hBA : (B : Set X) ⊆ A ∪ B := by
          intro z hz
          exact Or.inr hz
        exact interior_mono hBA
      -- enlarge the closure
      exact (closure_mono hsubset) hx_cl

theorem closure_equals_for_P1 {A : Set X} (hA : P1 A) : closure (interior A) = closure A := by
  apply le_antisymm
  · exact closure_mono interior_subset
  ·
    have h' : closure A ⊆ closure (closure (interior A)) := closure_mono hA
    simpa [closure_closure] using h'

theorem P3_iff_nbhd {A : Set X} : P3 A ↔ ∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure A := by
  classical
  constructor
  · intro hP3 x hxA
    have hxInt : x ∈ interior (closure A) := hP3 hxA
    rcases (mem_interior.1 hxInt) with ⟨U, hUsub, hUopen, hxU⟩
    exact ⟨U, hUopen, hxU, hUsub⟩
  · intro hnbhd x hxA
    rcases hnbhd x hxA with ⟨U, hUopen, hxU, hUsub⟩
    exact mem_interior.2 ⟨U, hUsub, hUopen, hxU⟩