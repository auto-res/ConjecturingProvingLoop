

theorem P2_of_P1_and_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : Topology.P1 (X:=X) A) (hDense : Dense A) : Topology.P2 (X:=X) A := by
  -- Unfold the definition of `P2`
  unfold Topology.P2
  intro x hx
  -- Step 1: from `P1` obtain `closure A ⊆ closure (interior A)`
  have h_closure_subset : (closure (A : Set X)) ⊆ closure (interior A) := by
    -- `P1` gives `A ⊆ closure (interior A)`; take closures and simplify
    have h' : closure (A : Set X) ⊆ closure (closure (interior A)) :=
      closure_mono h1
    simpa [closure_closure] using h'
  -- Step 2: since `A` is dense, `closure A = univ`
  have h_univ_subset : (Set.univ : Set X) ⊆ closure (interior A) := by
    simpa [hDense.closure_eq] using h_closure_subset
  -- Step 3: deduce `closure (interior A) = univ`
  have h_cl_eq_univ : closure (interior A) = (Set.univ : Set X) := by
    apply subset_antisymm
    · exact Set.subset_univ _
    · exact h_univ_subset
  -- Step 4: hence `interior (closure (interior A)) = univ`
  have h_int_eq_univ : interior (closure (interior A)) = (Set.univ : Set X) := by
    simpa [h_cl_eq_univ, interior_univ]
  -- Step 5: conclude the desired membership
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h_int_eq_univ] using this

theorem closure_eq_self_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P2 (X:=X) A) : closure A = closure (interior A) := by
  -- Obtain `P1` from the given `P2`
  have hP1 : Topology.P1 (X := X) A := Topology.P1_of_P2 (A := A) h
  -- Turn `P1` into the required equality
  simpa using ((Topology.P1_iff_closure_interior_subset (A := A)).1 hP1).symm

theorem exists_dense_P1 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, Dense A ∧ Topology.P1 (X:=X) A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simpa using dense_univ
  · simpa using (Topology.P1_univ (X := X))

theorem P1_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 (X:=X) A ↔ Topology.P3 (X:=X) A := by
  constructor
  · intro _; exact P3_of_open (X := X) (A := A) hA
  · intro _; exact P1_of_open (X := X) (A := A) hA

theorem P1_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} (h : Topology.P1 (X:=Y) B) : Topology.P1 (X:=X) (e ⁻¹' B) := by
  classical
  -- Step 1: transport `P1` through the inverse homeomorphism
  have hP1_image : Topology.P1 (X := X) (e.symm '' B) := by
    simpa using
      (Topology.P1_image_homeomorph (X := Y) (Y := X) (e := e.symm) (A := B) h)
  -- Step 2: identify the image with the preimage
  have h_eq : (e.symm '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      simpa using hyB
    · intro hx
      exact ⟨e x, hx, by
        simp [e.symm_apply_apply]⟩
  -- Step 3: rewrite and conclude
  simpa [h_eq] using hP1_image

theorem P3_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} (h : Topology.P3 (X:=Y) B) : Topology.P3 (X:=X) (e ⁻¹' B) := by
  classical
  -- Step 1: transport `P3` through the inverse homeomorphism
  have hP3_image : Topology.P3 (X := X) (e.symm '' B) := by
    simpa using
      (Topology.P3_image_homeomorph (X := Y) (Y := X) (e := e.symm) (A := B) h)
  -- Step 2: identify the image with the preimage
  have h_eq : (e.symm '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      simpa using hyB
    · intro hx
      exact ⟨e x, hx, by
        simp [e.symm_apply_apply]⟩
  -- Step 3: rewrite and conclude
  simpa [h_eq] using hP3_image