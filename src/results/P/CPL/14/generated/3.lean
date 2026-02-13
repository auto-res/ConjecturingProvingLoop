

theorem P3_empty {X} [TopologicalSpace X] : P3 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P2_iff_P3_of_closed {X} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 A ↔ P3 A := by
  constructor
  · intro hP2
    exact P3_of_P2 hP2
  · intro hP3
    -- First, show that `A ⊆ interior A`, hence `interior A = A`.
    have h_subset : (A : Set X) ⊆ interior A := by
      intro x hx
      have : x ∈ interior (closure A) := hP3 hx
      simpa [hA.closure_eq] using this
    have h_eq : (interior A : Set X) = A := by
      apply Set.Subset.antisymm
      · exact interior_subset
      · exact h_subset
    -- Therefore `A` is open.
    have hAopen : IsOpen A := by
      have : IsOpen (interior A) := isOpen_interior
      simpa [h_eq] using this
    -- Apply the open–set version of `P2`.
    exact P2_of_open hAopen

theorem P1_iff_P2_of_open {X} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ↔ P2 A := by
  constructor
  · intro _hP1
    exact P2_of_open hA
  · intro hP2
    exact P1_of_P2 hP2

theorem P2_union {X} [TopologicalSpace X] {A B : Set X} (hA : P2 A) (hB : P2 B) : P2 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` comes from `A`
      have hx_int : x ∈ interior (closure (interior A)) := hA hxA
      -- Monotonicity chain: `interior A ⊆ interior (A ∪ B)`
      have hsubset_int : interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      -- Hence `closure (interior A) ⊆ closure (interior (A ∪ B))`
      have hsubset_closure : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset_int
      -- Finally, take interiors again
      have hsubset :
          interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) :=
        interior_mono hsubset_closure
      exact hsubset hx_int
  | inr hxB =>
      -- `x` comes from `B`
      have hx_int : x ∈ interior (closure (interior B)) := hB hxB
      -- Monotonicity chain: `interior B ⊆ interior (A ∪ B)`
      have hsubset_int : interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      -- Hence `closure (interior B) ⊆ closure (interior (A ∪ B))`
      have hsubset_closure : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset_int
      -- Take interiors again
      have hsubset :
          interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) :=
        interior_mono hsubset_closure
      exact hsubset hx_int