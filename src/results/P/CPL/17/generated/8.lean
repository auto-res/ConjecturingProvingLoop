

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P1 A → Topology.P1 B → Topology.P1 (Set.prod A B) := by
  intro hP1A hP1B
  intro p hp
  rcases p with ⟨x, y⟩
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  have hx_cl : x ∈ closure (interior A) := hP1A hxA
  have hy_cl : y ∈ closure (interior B) := hP1B hyB
  -- The point lies in the product of the two closures
  have h_mem :
      (x, y) ∈ (closure (interior A)) ×ˢ (closure (interior B)) :=
    ⟨hx_cl, hy_cl⟩
  -- This product is contained in the desired closure
  have h_subset :
      (closure (interior A)) ×ˢ (closure (interior B)) ⊆
        closure (interior (A ×ˢ B)) := by
    intro q hq
    -- First place `q` in `closure ((interior A) ×ˢ (interior B))`
    have hq_in :
        q ∈ closure ((interior A) ×ˢ (interior B)) := by
      -- Identify the two closures
      have h_eq :
          closure ((interior A) ×ˢ (interior B)) =
            (closure (interior A)) ×ˢ (closure (interior B)) := by
        simpa using
          (closure_prod_eq :
            closure ((interior A) ×ˢ (interior B)) =
              (closure (interior A)) ×ˢ (closure (interior B)))
      simpa [h_eq] using hq
    -- Show the latter closure is inside `closure (interior (A ×ˢ B))`
    have h_mono :
        (interior A) ×ˢ (interior B) ⊆ interior (A ×ˢ B) := by
      intro r hr
      -- The rectangle is open and contained in `A ×ˢ B`
      have h_open : IsOpen ((interior A) ×ˢ (interior B)) :=
        (isOpen_interior).prod isOpen_interior
      have h_sub :
          ((interior A) ×ˢ (interior B)) ⊆ A ×ˢ B := by
        intro s hs
        exact
          ⟨ (interior_subset : interior A ⊆ A) hs.1,
            (interior_subset : interior B ⊆ B) hs.2 ⟩
      exact (interior_maximal h_sub h_open) hr
    have h_closure_mono :
        closure ((interior A) ×ˢ (interior B)) ⊆
          closure (interior (A ×ˢ B)) :=
      closure_mono h_mono
    exact h_closure_mono hq_in
  -- Conclude
  exact h_subset h_mem

theorem P3_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {B : Set Y} : Topology.P3 B → Topology.P3 (e ⁻¹' B) := by
  intro hP3B
  -- Transport `P3` through the inverse homeomorphism
  have hP3_image : Topology.P3 (e.symm '' B) :=
    (P3_image_homeomorph (e := e.symm) (A := B)) hP3B
  -- Identify the image by the inverse with the preimage by `e`
  have h_eq : (e.symm '' B) = (e ⁻¹' B) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change e (e.symm y) ∈ B
      simpa using hy
    · intro hx
      have hy : e x ∈ B := hx
      exact ⟨e x, hy, by
        simpa using e.symm_apply_apply x⟩
  -- Conclude via rewriting
  simpa [h_eq] using hP3_image

theorem P2_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] (A : Set X) : Topology.P2 A := by
  intro x hxA
  -- In a subsingleton, any nonempty set is the whole space.
  have hA_univ : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      have h_eq : y = x := Subsingleton.elim y x
      simpa [h_eq] using hxA
  -- The goal follows after rewriting with this fact.
  have : x ∈ interior (closure (interior A)) := by
    have hx_univ : x ∈ (Set.univ : Set X) := by
      trivial
    simpa [hA_univ, interior_univ, closure_univ] using hx_univ
  exact this