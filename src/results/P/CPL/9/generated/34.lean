

theorem P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (A := closure (interior A)) := by
  exact
    (P1_closure (A := interior A)) (by
      simpa using (P1_interior (A := A)))

theorem P3_prod_univ_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} (hB : Topology.P3 (A := B)) : Topology.P3 (A := Set.prod (Set.univ : Set X) B) := by
  -- `Set.univ : Set X` satisfies `P3`.
  have hA : Topology.P3 (A := (Set.univ : Set X)) := by
    simpa using Topology.P3_univ (X := X)
  simpa using
    Topology.P3_prod (A := (Set.univ : Set X)) (B := B) hA hB

theorem P3_iff_P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h_dense : Dense (interior A)) : Topology.P3 (A := A) ↔ Topology.P2 (A := A) := by
  constructor
  · intro hP3
    -- First, deduce `P1 A` from the density of `interior A`.
    have hP1 : P1 (A := A) := by
      intro x hx
      -- Since `interior A` is dense, its closure is the whole space.
      have h_closure_univ :
          (closure (interior A) : Set X) = (Set.univ : Set X) := by
        simpa using h_dense.closure_eq
      -- Hence every point lies in this closure.
      have : (x : X) ∈ (Set.univ : Set X) := by
        simp
      simpa [h_closure_univ] using this
    -- Combine `P1` and the given `P3` to obtain `P2`.
    exact P1_and_P3_imp_P2 (A := A) hP1 hP3
  · intro hP2
    exact P2_imp_P3 (A := A) hP2

theorem P2_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P2 (A := Set.prod A B) ↔ Topology.P2 (A := Set.prod B A) := by
  classical
  -- The homeomorphism swapping the coordinates.
  let e : X × Y ≃ₜ Y × X := Homeomorph.prodComm X Y
  ----------------------------------------------------------------
  -- 1.  The image of `A × B` under `e` is `B × A`.
  ----------------------------------------------------------------
  have h_image :
      (e '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases q with ⟨x, y⟩
      rcases hq with ⟨hxA, hyB⟩
      simpa [e, Homeomorph.prodComm, Set.prod] using And.intro hyB hxA
    · intro hp
      rcases p with ⟨y, x⟩
      have h : y ∈ B ∧ x ∈ A := by
        simpa [Set.prod] using hp
      rcases h with ⟨hyB, hxA⟩
      have hq : ((x, y) : X × Y) ∈ Set.prod A B := by
        simpa [Set.prod] using And.intro hxA hyB
      have : (y, x) ∈ (e '' Set.prod A B : Set (Y × X)) := by
        refine ⟨(x, y), hq, ?_⟩
        simp [e, Homeomorph.prodComm]
      simpa using this
  ----------------------------------------------------------------
  -- 2.  The image of `B × A` under `e.symm` is `A × B`.
  ----------------------------------------------------------------
  have h_image_symm :
      (e.symm '' (Set.prod B A) : Set (X × Y)) = Set.prod A B := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases q with ⟨y, x⟩
      rcases hq with ⟨hyB, hxA⟩
      simpa [e, Homeomorph.prodComm, Set.prod] using And.intro hxA hyB
    · intro hp
      rcases p with ⟨x, y⟩
      have h : x ∈ A ∧ y ∈ B := by
        simpa [Set.prod] using hp
      rcases h with ⟨hxA, hyB⟩
      have hq : ((y, x) : Y × X) ∈ Set.prod B A := by
        simpa [Set.prod] using And.intro hyB hxA
      have : (x, y) ∈ (e.symm '' Set.prod B A : Set (X × Y)) := by
        refine ⟨(y, x), hq, ?_⟩
        simp [e, Homeomorph.prodComm]
      simpa using this
  ----------------------------------------------------------------
  -- 3.  Transport the `P2` property along the homeomorphism.
  ----------------------------------------------------------------
  refine ⟨?_, ?_⟩
  · intro hP2
    have hImage : Topology.P2 (A := e '' Set.prod A B) :=
      P2_image_homeomorph (e := e) (A := Set.prod A B) hP2
    simpa [h_image] using hImage
  · intro hP2
    have hImage : Topology.P2 (A := e.symm '' Set.prod B A) :=
      P2_image_homeomorph (e := e.symm) (A := Set.prod B A) hP2
    simpa [h_image_symm] using hImage

theorem P1_dense_interior_iff {X : Type*} [TopologicalSpace X] {A : Set X} : Dense (interior A) → (Topology.P1 (A := A) ↔ closure A = closure (interior A)) := by
  intro _
  simpa [eq_comm] using (P1_iff_closure_eq (A := A))

theorem P3_closed_of_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} (hclosed : IsClosed A) (h_eq : interior A = A) : Topology.P3 (A := A) := by
  intro x hx
  simpa [hclosed.closure_eq, h_eq] using hx

theorem P3_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P3 (A := A) := by
  intro x hx
  classical
  -- In a subsingleton space, a non-empty set is the whole space.
  have hA_univ : (A : Set X) = (Set.univ : Set X) := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      have h_eq : y = x := Subsingleton.elim y x
      simpa [h_eq] using hx
  -- Rewrite the goal using `hA_univ`.
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [hA_univ, closure_univ, interior_univ] using this