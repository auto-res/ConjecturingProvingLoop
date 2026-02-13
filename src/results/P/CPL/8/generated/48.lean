

theorem P1_prod_assoc {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P1 (Set.prod A (Set.prod B C)) ↔ P1 (Set.prod (Set.prod A B) C) := by
  -- The associator homeomorphism, oriented so that it sends `(x , (y , z))`
  -- to `((x , y) , z)`.
  let f : X × (Y × Z) ≃ₜ (X × Y) × Z := (Homeomorph.prodAssoc X Y Z).symm
  -- First, identify the image of `A × (B × C)` under `f`.
  have hImage :
      (f '' (Set.prod A (Set.prod B C)) : Set ((X × Y) × Z)) =
        Set.prod (Set.prod A B) C := by
    ext p
    constructor
    · -- Forward direction.
      rintro ⟨q, hq, rfl⟩
      rcases q with ⟨x, yz⟩
      rcases yz with ⟨y, z⟩
      rcases hq with ⟨hxA, hYZ⟩
      rcases hYZ with ⟨hyB, hzC⟩
      -- After unfolding, everything is by `simp`.
      simp [f, Homeomorph.prodAssoc, Set.prod, hxA, hyB, hzC]
    · -- Reverse direction.
      intro hp
      rcases p with ⟨⟨x, y⟩, z⟩
      rcases hp with ⟨hxy, hzC⟩
      rcases hxy with ⟨hxA, hyB⟩
      -- Build a preimage point.
      let q : X × (Y × Z) := (x, (y, z))
      have hq : q ∈ Set.prod A (Set.prod B C) := by
        dsimp [Set.prod, q]
        exact And.intro hxA (And.intro hyB hzC)
      refine ⟨q, hq, ?_⟩
      simp [q, f, Homeomorph.prodAssoc]
  -- Transport `P1` via the homeomorphism and rewrite with `hImage`.
  simpa [hImage] using
    (P1_homeomorph_iff (f := f) (A := Set.prod A (Set.prod B C)))

theorem P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} : P2 A → P2 B → P2 C → P2 (A ∪ B ∪ C) := by
  intro hA hB hC
  have hAB : P2 (A ∪ B) := P2_union (A := A) (B := B) hA hB
  have hABC : P2 ((A ∪ B) ∪ C) :=
    P2_union (A := (A ∪ B)) (B := C) hAB hC
  simpa [Set.union_assoc] using hABC

theorem P1_iff_P2_of_closure_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hDense : closure A = Set.univ) : P1 A ↔ P2 A := by
  refine ⟨?forward, ?backward⟩
  · intro hP1
    -- First, `hP1` gives equality of the two closures.
    have h_cl_eq : closure (interior (A : Set X)) = closure A :=
      closure_interior_eq_of_P1 (A := A) hP1
    -- Using the density assumption, this closure is all of `univ`.
    have h_cl_univ : closure (interior A) = Set.univ := by
      simpa [hDense] using h_cl_eq
    -- From this density we know `P2 A ↔ P3 A`.
    have h_equiv : P2 A ↔ P3 A :=
      (P2_iff_P3_of_interior_dense (A := A)) h_cl_univ
    -- And `P3 A` holds because `closure A = univ`.
    have hP3 : P3 A := P3_of_dense (A := A) hDense
    -- Hence `P2 A`.
    exact (h_equiv.2) hP3
  · intro hP2
    exact P2_to_P1 (A := A) hP2