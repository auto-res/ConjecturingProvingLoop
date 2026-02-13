

theorem P2_sigma_type {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P2 (A i)) : P2 {x : X | ∃ i, x ∈ A i} := by
  -- First, obtain `P2` for the union `⋃ i, A i`.
  have hP2_union : P2 (⋃ i, A i) := P2_unionᵢ (A := A) h
  -- Identify the σ–type set with the union.
  have h_eq : ({x : X | ∃ i, x ∈ A i} : Set X) = ⋃ i, A i := by
    ext x
    constructor
    · rintro ⟨i, hi⟩
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
      exact ⟨i, hi⟩
  -- Transfer the `P2` property along the equality.
  intro x hx
  have hx_union : x ∈ ⋃ i, A i := by
    simpa [h_eq] using hx
  have hx_int : x ∈ interior (closure (interior (⋃ i, A i))) :=
    hP2_union hx_union
  simpa [h_eq] using hx_int

theorem P1_prod_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P1 A) (hB : P1 B) : P1 (Set.image (fun p : X × Y => (p.1, p.2)) (Set.prod A B)) := by
  -- The map `p ↦ (p.1, p.2)` is the identity, hence its image is the product itself.
  have h_eq :
      (Set.image (fun p : X × Y => (p.1, p.2)) (Set.prod A B) :
        Set (X × Y)) = Set.prod A B := by
    ext p
    constructor
    · rintro ⟨⟨x, y⟩, hxy, rfl⟩
      exact hxy
    · intro hp
      refine ⟨p, hp, ?_⟩
      cases p with
      | mk x y => simp
  -- Apply `P1` for the product `A ×ˢ B` and rewrite using `h_eq`.
  simpa [h_eq] using (P1_prod (A := A) (B := B) hA hB)

theorem P2_iterate_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior (interior (interior A))) := by
  exact
    P2_of_isOpen
      (A := interior (interior (interior A)))
      isOpen_interior