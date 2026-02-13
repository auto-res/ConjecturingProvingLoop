

theorem P3_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} : Topology.P3 B → Topology.P3 (e ⁻¹' B) := by
  intro hP3B
  -- 1. Transport `P3 B` along the inverse homeomorphism.
  have hImage : Topology.P3 (e.symm '' B) := by
    simpa using (P3_image_homeomorph (e := e.symm) (A := B) hP3B)
  -- 2. Identify `e.symm '' B` with the preimage `e ⁻¹' B`.
  have h_eq : (e.symm '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      simpa using hyB
    · intro hx
      exact ⟨e x, hx, by simpa using e.symm_apply_apply x⟩
  -- 3. Use `hImage` to obtain the desired inclusion.
  intro x hx
  -- Regard `x` as an element of `e.symm '' B`.
  have hx_image : x ∈ (e.symm '' B : Set X) :=
    ⟨e x, hx, by simpa using e.symm_apply_apply x⟩
  -- Apply `P3` for that set.
  have hx_int : x ∈ interior (closure (e.symm '' B)) := hImage hx_image
  -- Rewrite using the identified sets.
  simpa [h_eq] using hx_int

theorem P2_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} : Topology.P2 A := by
  simpa using (P2_of_open (A := A) (isOpen_discrete _))

theorem P3_prod_univ_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : Topology.P3 A → Topology.P3 (A ×ˢ (Set.univ : Set Y)) := by
  intro hP3A
  -- `univ` in `Y` trivially satisfies `P3`.
  have hP3_univ : Topology.P3 (Set.univ : Set Y) := by
    simpa using (Topology.P3_univ (X := Y))
  -- Apply the product lemma.
  simpa using
    (Topology.P3_prod (A := A) (B := (Set.univ : Set Y)) hP3A hP3_univ)