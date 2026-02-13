

theorem P2_compact_subsets_are_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : (∀ C, C ⊆ A → IsCompact C → P2 C) → P1 A := by
  intro h
  -- We must show: `A ⊆ closure (interior A)`.
  intro x hxA
  ----------------------------------------------------------------
  -- 1. Apply the hypothesis to the compact singleton `{x}`.
  ----------------------------------------------------------------
  have h_subset_single : ({x} : Set X) ⊆ A := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy] ; exact hxA
  have h_compact_single : IsCompact ({x} : Set X) := isCompact_singleton
  have hP2_single : P2 ({x} : Set X) :=
    h ({x}) h_subset_single h_compact_single
  -- Hence `x` belongs to the interior of the closure of the interior
  -- of its singleton.
  have hx_in :
      x ∈ interior (closure (interior ({x} : Set X))) := by
    have : x ∈ ({x} : Set X) := by simp
    exact hP2_single this
  ----------------------------------------------------------------
  -- 2. Show that `interior {x}` is non-empty (otherwise contradiction).
  ----------------------------------------------------------------
  have hInt_nonempty : (interior ({x} : Set X)).Nonempty := by
    by_contra hcontr
    have hInt_empty :
        interior ({x} : Set X) = (∅ : Set X) :=
      Set.not_nonempty_iff_eq_empty.1 hcontr
    have : x ∈ (∅ : Set X) := by
      simpa [hInt_empty, closure_empty, interior_empty] using hx_in
    simpa using this
  -- Obtain a point `y` in `interior {x}`; necessarily `y = x`.
  rcases hInt_nonempty with ⟨y, hyInt⟩
  have hy_eq : y = x := by
    have : y ∈ ({x} : Set X) := interior_subset hyInt
    simpa [Set.mem_singleton_iff] using this
  have hx_int_single : x ∈ interior ({x} : Set X) := by
    simpa [hy_eq] using hyInt
  ----------------------------------------------------------------
  -- 3. `interior {x}` sits inside `interior A`, so `x ∈ interior A`.
  ----------------------------------------------------------------
  have h_int_subset : interior ({x} : Set X) ⊆ interior A := by
    apply interior_mono
    exact h_subset_single
  have hx_intA : x ∈ interior A := h_int_subset hx_int_single
  ----------------------------------------------------------------
  -- 4. Conclude `x ∈ closure (interior A)`.
  ----------------------------------------------------------------
  exact subset_closure hx_intA

theorem P1_of_exhaustion {X : Type*} [TopologicalSpace X] {A : Set X} (K : ℕ → Set X) : (∀ n, K n ⊆ K (n + 1)) → (⋃ n, K n) = A → (∀ n, P1 (K n)) → P1 A := by
  intro hMono hUnion hP1K
  -- touch `hMono` to avoid an unused-argument warning
  have _ := hMono 0
  intro x hxA
  -- Rewrite `hxA` using the union identity.
  have hxUnion : x ∈ ⋃ n, K n := by
    simpa [hUnion] using hxA
  -- Pick an index with `x ∈ K n`.
  rcases Set.mem_iUnion.1 hxUnion with ⟨n, hxKn⟩
  -- Apply the `P1` property for `K n`.
  have hP1n : P1 (K n) := hP1K n
  have hx_cl : x ∈ closure (interior (K n)) := hP1n hxKn
  -- Show `interior (K n) ⊆ interior A`.
  have hKn_subset_A : (K n : Set X) ⊆ A := by
    intro y hy
    have : (y : X) ∈ (⋃ m, K m) := by
      exact Set.mem_iUnion.2 ⟨n, hy⟩
    simpa [hUnion] using this
  have hSubset : interior (K n) ⊆ interior A :=
    interior_mono hKn_subset_A
  -- Taking closures preserves inclusions.
  have hx_clA : x ∈ closure (interior A) :=
    (closure_mono hSubset) hx_cl
  exact hx_clA