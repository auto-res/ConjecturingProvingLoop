

theorem P1_dense_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (h_dense : closure (interior A) = Set.univ) : closure (interior (e '' A)) = Set.univ := by
  -- Step 1: relate the two closures through the homeomorphism `e`.
  have h1 : closure (interior (e '' A)) = (⇑e) '' closure (interior A) := by
    -- `e.image_closure` gives the image of a closure,
    -- `e.image_interior` the image of an interior.
    have h_cl : (⇑e) '' closure (interior A) =
        closure ((⇑e) '' interior A) := by
      simpa using e.image_closure (s := interior A)
    have h_int : (⇑e) '' interior A = interior (e '' A) := by
      simpa using e.image_interior (s := A)
    simpa [h_int] using h_cl.symm
  -- Step 2: use the density hypothesis.
  have h2 : closure (interior (e '' A)) = (⇑e) '' (Set.univ : Set X) := by
    simpa [h_dense] using h1
  -- Step 3: the image of `univ` under a surjective map is `univ`.
  have h3 : (⇑e) '' (Set.univ : Set X) = (Set.univ : Set Y) := by
    ext y
    constructor
    · intro _; trivial
    · intro _; rcases e.surjective y with ⟨x, rfl⟩; exact ⟨x, trivial, rfl⟩
  -- Step 4: conclude.
  simpa [h3] using h2

theorem P1_prod_distrib {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P1 A) (hBC : P1 (Set.prod B C)) : P1 (Set.prod (Set.prod A B) C) := by
  classical
  ----------------------------------------------------------------
  -- 1.  First build `P1` for `A ×ˢ (B ×ˢ C)`.
  ----------------------------------------------------------------
  have hABC : P1 (Set.prod A (Set.prod B C)) := P1_prod hA hBC
  ----------------------------------------------------------------
  -- 2.  Transport this property with the associativity homeomorphism
  --     `(X × (Y × Z)) ≃ ((X × Y) × Z)`.
  ----------------------------------------------------------------
  let e : (X × (Y × Z)) ≃ₜ ((X × Y) × Z) :=
    (Homeomorph.prodAssoc X Y Z).symm
  have hImage : P1 (e '' Set.prod A (Set.prod B C)) :=
    P1_image_homeomorph e hABC
  ----------------------------------------------------------------
  -- 3.  Identify the image with `(A ×ˢ B) ×ˢ C`.
  ----------------------------------------------------------------
  have h_eq :
      (e '' Set.prod A (Set.prod B C)) = Set.prod (Set.prod A B) C := by
    ext p
    constructor
    · -- `→`
      rintro ⟨q, hq, rfl⟩
      --  `q : X × (Y × Z)`
      rcases q with ⟨a, bc⟩
      rcases bc with ⟨b, c⟩
      rcases hq with ⟨ha, hbc⟩
      rcases hbc with ⟨hb, hc⟩
      --  Unfold the map `e` and the definition of `Set.prod`.
      dsimp [e, Homeomorph.prodAssoc, Set.prod] at *
      exact And.intro (And.intro ha hb) hc
    · -- `←`
      intro hp
      --  Decompose `p` and the membership hypothesis.
      rcases p with ⟨⟨a, b⟩, c⟩
      dsimp [Set.prod] at hp
      rcases hp with ⟨hab, hc⟩
      rcases hab with ⟨ha, hb⟩
      --  Build the pre-image point and the required witnesses.
      refine ⟨(a, (b, c)), ?_, ?_⟩
      · dsimp [Set.prod]
        exact And.intro ha (And.intro hb hc)
      · simp [e, Homeomorph.prodAssoc]
  ----------------------------------------------------------------
  -- 4.  Rewrite with the identified equality and conclude.
  ----------------------------------------------------------------
  simpa [h_eq] using hImage

theorem P3_of_closed_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} (h_closed : IsClosed A) (h_eq : interior A = A) : P3 A := by
  -- Since `interior A = A`, the set `A` is open.
  have h_open : IsOpen A := by
    simpa [h_eq] using (isOpen_interior : IsOpen (interior A))
  -- Apply the lemma for open sets.
  exact P3_open h_open