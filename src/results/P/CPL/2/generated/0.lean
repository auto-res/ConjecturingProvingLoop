

theorem P1_of_P2 {A : Set X} (h : P2 A) : P1 A := by
  unfold P1 P2 at *
  exact subset_trans h interior_subset

theorem exists_set_with_P3 [Nonempty X] : ∃ A : Set X, P3 A := by
  exact ⟨(∅ : Set X), by
    simp [P3]⟩

theorem P1_iff_closure_interior_subset {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  unfold P1
  constructor
  · intro h
    apply subset_antisymm
    · exact closure_mono interior_subset
    ·
      have h' : closure A ⊆ closure (closure (interior A)) := closure_mono h
      simpa [closure_closure] using h'
  · intro h_eq
    have : (A : Set X) ⊆ closure A := subset_closure
    simpa [h_eq] using this

theorem interior_subset_of_P2 {A : Set X} (h : P2 A) : interior A ⊆ interior (closure (interior A)) := subset_trans interior_subset h

theorem closure_eq_of_P3 {A : Set X} (h : P3 A) : closure A = closure (interior (closure A)) := by
  apply subset_antisymm
  · exact closure_mono h
  ·
    have : interior (closure A) ⊆ closure A := interior_subset
    simpa [closure_closure] using closure_mono this

theorem P1_union {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  -- expand the definition of `P1`
  unfold P1 at hA hB ⊢
  -- we prove the required subset relation point-wise
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hx_clA : x ∈ closure (interior A) := hA hxA
      -- enlarge the set via monotonicity of `interior` and `closure`
      have h_sub : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact h_sub hx_clA
  | inr hxB =>
      -- `x ∈ B`
      have hx_clB : x ∈ closure (interior B) := hB hxB
      have h_sub : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact h_sub hx_clB

theorem P2_image_homeomorph {Y : Type*} [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (h : P2 A) : P2 (e '' A) := by
  classical
  -- unpack the definition of `P2`
  unfold P2 at h ⊢
  intro y hy
  -- choose a preimage of `y`
  rcases hy with ⟨x, hxA, rfl⟩
  -- apply the hypothesis on `A`
  have hx : x ∈ interior (closure (interior A)) := h hxA
  -- Step 1: transport through `e`
  have hx1 : e x ∈ interior (e '' closure (interior A)) := by
    -- first, `e x` lies in the image of the interior
    have hmem : (e x) ∈ (e '' interior (closure (interior A))) := ⟨x, hx, rfl⟩
    -- translate via `image_interior`
    have h_eq :
        (e '' interior (closure (interior A)) : Set _) =
          interior (e '' closure (interior A)) := by
      simpa using e.image_interior (s := closure (interior A))
    simpa [h_eq] using hmem
  -- Step 2: rewrite the closure with `image_closure`
  have hx2 : e x ∈ interior (closure (e '' interior A)) := by
    have h_eq :
        (e '' closure (interior A) : Set _) = closure (e '' interior A) := by
      simpa using e.image_closure (s := interior A)
    simpa [h_eq] using hx1
  -- Step 3: identify `e '' interior A` with `interior (e '' A)`
  have hx3 : e x ∈ interior (closure (interior (e '' A))) := by
    have h_eq : (e '' interior A : Set _) = interior (e '' A) := by
      simpa using e.image_interior (s := A)
    simpa [h_eq] using hx2
  -- done
  exact hx3

theorem P1_empty : P1 (∅ : Set X) := by
  unfold P1
  simp

theorem P3_univ : P3 (Set.univ : Set X) := by
  simp [P3]