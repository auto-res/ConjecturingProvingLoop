

theorem P1_iff_dense_int {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  unfold P1
  constructor
  · intro hA
    apply le_antisymm
    · exact closure_mono (interior_subset : interior A ⊆ A)
    ·
      have hClosed : IsClosed (closure (interior A)) := isClosed_closure
      exact closure_minimal hA hClosed
  · intro hEq
    have : (A : Set X) ⊆ closure A := subset_closure
    simpa [hEq] using this

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro hA
  exact subset_trans hA interior_subset

theorem P2_open_sets {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A := by
  unfold P2
  have hInt : interior A = A := hA.interior_eq
  have hSub : (A : Set X) ⊆ interior (closure A) :=
    interior_maximal subset_closure hA
  simpa [hInt] using hSub

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  -- Unfold the definition of `P1` in hypotheses and goal
  unfold P1 at *
  -- Helper inclusions: the closures of the interiors of `A` and `B`
  -- are contained in the closure of the interior of `A ∪ B`.
  have hClA :
      closure (interior A) ⊆ closure (interior (A ∪ B)) :=
    closure_mono
      (interior_mono
        (Set.subset_union_left : (A : Set X) ⊆ A ∪ B))
  have hClB :
      closure (interior B) ⊆ closure (interior (A ∪ B)) :=
    closure_mono
      (interior_mono
        (Set.subset_union_right : (B : Set X) ⊆ A ∪ B))
  -- Prove the desired inclusion
  intro x hx
  cases hx with
  | inl hxA =>
      have : x ∈ closure (interior A) := hA hxA
      exact hClA this
  | inr hxB =>
      have : x ∈ closure (interior B) := hB hxB
      exact hClB this

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, P3 A) : P3 (⋃₀ 𝒜) := by
  -- Expand the definition of `P3` in the hypothesis
  unfold P3 at h
  -- Goal: `(⋃₀ 𝒜) ⊆ interior (closure (⋃₀ 𝒜))`
  intro x hx
  -- Find a set `A ∈ 𝒜` that contains `x`
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  -- `x` is in `interior (closure A)` thanks to `P3 A`
  have hx_in_int_clA : x ∈ interior (closure A) := (h A hA_mem) hxA
  -- Show `closure A ⊆ closure (⋃₀ 𝒜)`
  have hA_subset : (A : Set X) ⊆ ⋃₀ 𝒜 := by
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  have h_closure_subset : closure A ⊆ closure (⋃₀ 𝒜) :=
    closure_mono hA_subset
  -- Hence, their interiors satisfy the same inclusion
  have h_int_subset : interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) :=
    interior_mono h_closure_subset
  -- Conclude
  exact h_int_subset hx_in_int_clA