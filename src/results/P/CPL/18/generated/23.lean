

theorem P1_closed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (hP3 : Topology.P3 A) : Topology.P1 A := by
  have hP2 : Topology.P2 A := (P2_iff_P3_of_closed (X := X) (A := A) hA).2 hP3
  exact P2_implies_P1 (A := A) hP2

theorem P1_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (h : Topology.P1 (A.prod B)) : Topology.P1 (B.prod A) := by
  -- Transport the property through the coordinate swap homeomorphism.
  have h_image :
      Topology.P1
        ((fun p : X × Y => Prod.swap p) '' (A.prod B) : Set (Y × X)) := by
    simpa using
      (P1_image_homeomorph
          (e := Homeomorph.prodComm (X := X) (Y := Y))
          (A := A.prod B)) h
  -- Identify this image with `B × A`.
  have h_eq :
      ((fun p : X × Y => Prod.swap p) '' (A.prod B) : Set (Y × X)) =
        B.prod A := by
    ext p
    constructor
    · rintro ⟨⟨x, y⟩, hxy, rfl⟩
      rcases hxy with ⟨hxA, hyB⟩
      exact And.intro hyB hxA
    · intro hp
      rcases p with ⟨y, x⟩
      rcases hp with ⟨hyB, hxA⟩
      refine ⟨(x, y), ?_, rfl⟩
      exact And.intro hxA hyB
  -- Conclude using this identification.
  simpa [h_eq] using h_image

theorem exists_open_P1_dense {X : Type*} [TopologicalSpace X] : ∃ U : Set X, IsOpen U ∧ Dense U ∧ Topology.P1 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, ?_, ?_⟩
  · exact dense_univ
  · simpa using (P1_univ (X := X))

theorem P1_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P1 A) (hB : IsClosed B) : Topology.P1 (A \ B) := by
  -- Unfold the definition of `P1` in the hypothesis and in the goal.
  dsimp [Topology.P1] at hA ⊢
  -- Take an arbitrary point of `A \ B`.
  intro x hx
  rcases hx with ⟨hxA, hx_notB⟩
  -- Use the hypothesis `hA`.
  have hx_cl : x ∈ closure (interior (A : Set X)) := hA hxA
  -- Neighbourhood characterization of the closure.
  have h_prop := (mem_closure_iff).1 hx_cl
  -- We prove that every open neighbourhood of `x` meets
  -- `interior (A \ B)`, hence `x` is in its closure.
  apply (mem_closure_iff).2
  intro W hW_open hxW
  /- Consider the open set `V = W \ B`, which still contains `x`
     and avoids `B`. -/
  have hV_open : IsOpen (W \ B) := by
    have hB_open : IsOpen (Bᶜ) := hB.isOpen_compl
    simpa [Set.diff_eq] using hW_open.inter hB_open
  have hxV : x ∈ W \ B := by
    exact And.intro hxW hx_notB
  -- Apply `h_prop` to `V` to obtain a point of `interior A` in `V`.
  have h_nonempty : ((W \ B) ∩ interior (A : Set X)).Nonempty :=
    h_prop (W \ B) hV_open hxV
  rcases h_nonempty with ⟨y, hyV, hy_intA⟩
  have hyW    : y ∈ W := hyV.1
  have hy_notB : y ∉ B := hyV.2
  -- Show that `y ∈ interior (A \ B)`.
  have hy_int_diff : y ∈ interior (A \ B) := by
    -- The set `S = interior A \ B` is open and contained in `A \ B`,
    -- hence contained in `interior (A \ B)`.
    have hS_open : IsOpen (interior (A : Set X) \ B) := by
      have hB_open : IsOpen (Bᶜ) := hB.isOpen_compl
      simpa [Set.diff_eq] using isOpen_interior.inter hB_open
    have hS_subset :
        (interior (A : Set X) \ B : Set X) ⊆ interior (A \ B) :=
      interior_maximal
        (by
          intro z hz
          rcases hz with ⟨hz_intA, hz_notB⟩
          exact And.intro (interior_subset hz_intA) hz_notB)
        hS_open
    have : y ∈ interior (A : Set X) \ B := And.intro hy_intA hy_notB
    exact hS_subset this
  -- Provide the required witness in `W ∩ interior (A \ B)`.
  exact ⟨y, And.intro hyW hy_int_diff⟩

theorem P2_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hx
  classical
  -- Either `A` is empty or it coincides with `univ`
  by_cases hAempty : (A : Set X) = ∅
  · -- The empty case is impossible since `x ∈ A`
    have : (x ∈ (∅ : Set X)) := by
      simpa [hAempty] using hx
    cases this
  · -- Hence `A = univ`
    have hAuniv : (A : Set X) = (Set.univ : Set X) := by
      ext z
      constructor
      · intro _; trivial
      · intro _
        have hz : z = x := Subsingleton.elim _ _
        simpa [hz] using hx
    -- The required membership is now trivial
    have : x ∈ (Set.univ : Set X) := by
      trivial
    simpa [hAuniv, interior_univ, closure_univ] using this