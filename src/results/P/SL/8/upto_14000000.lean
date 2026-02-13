

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P1] at hP2 ⊢
  exact Set.Subset.trans hP2 interior_subset

theorem P2_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P3] at hP2 ⊢
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hcl : closure (interior A) ⊆ closure A := by
      have : interior A ⊆ A := interior_subset
      exact closure_mono this
    exact interior_mono hcl
  exact Set.Subset.trans hP2 hsubset

theorem isOpen_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  have h : interior A ⊆ interior (closure A) := interior_mono subset_closure
  simpa [hA.interior_eq] using h

theorem interior_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior A) := by
  dsimp [Topology.P2]
  simpa [interior_interior] using
    (interior_mono (subset_closure : interior A ⊆ closure (interior A)))

theorem interior_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior A) := by
  have hA : IsOpen (interior A) := isOpen_interior
  simpa using Topology.isOpen_imp_P3 hA

theorem interior_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior A) := by
  dsimp [Topology.P1]
  simpa [interior_interior] using
    (subset_closure : interior A ⊆ closure (interior A))

theorem dense_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure A = (Set.univ : Set X)) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  have hIntCl : interior (closure A) = (Set.univ : Set X) := by
    have : interior (closure A) = interior (Set.univ : Set X) := by
      simpa [hA]
    simpa [interior_univ] using this
  have hAu : A ⊆ (Set.univ : Set X) := by
    intro x hx
    trivial
  simpa [hIntCl] using hAu

theorem isOpen_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A := by
  dsimp [Topology.P1]
  simpa [hA.interior_eq] using (subset_closure : A ⊆ closure A)

theorem isOpen_imp_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P2 A := by
  dsimp [Topology.P2]
  have hP3 := (Topology.isOpen_imp_P3 (X := X) (A := A) hA)
  dsimp [Topology.P3] at hP3
  simpa [hA.interior_eq] using hP3

theorem closed_P3_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    IsOpen A := by
  have hcl : closure A = A := hA_closed.closure_eq
  have hsubset : A ⊆ interior A := by
    dsimp [Topology.P3] at hP3
    simpa [hcl] using hP3
  have hint : interior A ⊆ A := interior_subset
  have heq : interior A = A := Set.Subset.antisymm hint hsubset
  have : IsOpen (interior A) := isOpen_interior
  simpa [heq] using this

theorem isOpen_P2_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    exact Topology.P2_imp_P3 (X := X) (A := A) hP2
  · intro hP3
    dsimp [Topology.P2, Topology.P3] at hP3 ⊢
    simpa [hA.interior_eq] using hP3

theorem closed_P2_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) :
    IsOpen A := by
  have hP3 : Topology.P3 A :=
    Topology.P2_imp_P3 (X := X) (A := A) hP2
  exact Topology.closed_P3_isOpen (X := X) (A := A) hA_closed hP3

theorem isOpen_P1_iff_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro _hP1
    exact Topology.isOpen_imp_P2 (X := X) (A := A) hA
  · intro hP2
    exact Topology.P2_imp_P1 (X := X) (A := A) hP2

theorem isOpen_P1_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ↔ Topology.P3 A := by
  have h12 : Topology.P1 A ↔ Topology.P2 A :=
    Topology.isOpen_P1_iff_P2 (X := X) (A := A) hA
  have h23 : Topology.P2 A ↔ Topology.P3 A :=
    Topology.isOpen_P2_iff_P3 (X := X) (A := A) hA
  exact h12.trans h23

theorem closed_P3_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P3 A ↔ IsOpen A := by
  constructor
  · intro hP3
    exact Topology.closed_P3_isOpen (X := X) (A := A) hA_closed hP3
  · intro hA_open
    exact Topology.isOpen_imp_P3 (X := X) (A := A) hA_open

theorem interior_closure_interior_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  have h_closure : closure (interior A) ⊆ closure A := by
    have h_subset : interior A ⊆ A := interior_subset
    exact closure_mono h_subset
  exact interior_mono h_closure

theorem closure_interior_eq_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : closure (interior A) = closure A := by
  simpa [hA.interior_eq]

theorem closed_P1_iff_closure_interior_eq {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) :
    Topology.P1 A ↔ closure (interior A) = A := by
  constructor
  · intro hP1
    dsimp [Topology.P1] at hP1
    have h_subset₁ : closure (interior A) ⊆ A := by
      have h_int : interior A ⊆ A := interior_subset
      have h_clos : closure (interior A) ⊆ closure A := closure_mono h_int
      simpa [hA_closed.closure_eq] using h_clos
    exact Set.Subset.antisymm h_subset₁ hP1
  · intro h_eq
    dsimp [Topology.P1]
    have h : A ⊆ A := subset_rfl
    simpa [h_eq] using h

theorem closed_P2_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A ↔ IsOpen A := by
  constructor
  · intro hP2
    exact Topology.closed_P2_isOpen (X := X) (A := A) hA_closed hP2
  · intro hA_open
    exact Topology.isOpen_imp_P2 (X := X) (A := A) hA_open

theorem closed_P2_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    exact Topology.P2_imp_P3 (X := X) (A := A) hP2
  · intro hP3
    have hA_open : IsOpen A :=
      Topology.closed_P3_isOpen (X := X) (A := A) hA_closed hP3
    exact Topology.isOpen_imp_P2 (X := X) (A := A) hA_open

theorem closure_interior_eq_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (interior A) = A) :
    Topology.P1 A := by
  dsimp [Topology.P1]
  simpa [hA] using (subset_rfl : A ⊆ A)

theorem P1_imp_closure_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) :
    closure (interior A) = closure A := by
  dsimp [Topology.P1] at hP1
  apply Set.Subset.antisymm
  · -- `closure (interior A)` is contained in `closure A`
    have h : interior A ⊆ A := interior_subset
    exact closure_mono h
  · -- `closure A` is contained in `closure (interior A)`
    have h_cl : A ⊆ closure (interior A) := hP1
    have : closure A ⊆ closure (closure (interior A)) := closure_mono h_cl
    simpa [closure_closure] using this

theorem Topology.P3_nonempty_interiorClosure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 A) (hA : A.Nonempty) :
    (interior (closure A)).Nonempty := by
  rcases hA with ⟨x, hx⟩
  exact ⟨x, hP3 hx⟩

theorem interior_closure_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (closure A)) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  simpa using
    Topology.isOpen_imp_P3 (X := X) (A := interior (closure A)) h_open

theorem interior_closure_interior_eq_interior_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    interior (closure (interior A)) = interior (closure A) := by
  have h : closure (interior A) = closure A :=
    Topology.closure_interior_eq_of_isOpen (X := X) (A := A) hA
  simpa [h]

theorem P2_imp_closure_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) :
    closure (interior A) = closure A := by
  have hP1 : Topology.P1 A :=
    Topology.P2_imp_P1 (X := X) (A := A) hP2
  exact P1_imp_closure_interior_eq_closure (X := X) (A := A) hP1

theorem denseInterior_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P1 A := by
  dsimp [Topology.P1]
  have : A ⊆ (Set.univ : Set X) := Set.subset_univ _
  simpa [h_dense] using this

theorem interior_closure_interior_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (closure (interior A))) := by
  have h_open : IsOpen (interior (closure (interior A))) := isOpen_interior
  simpa using
    Topology.isOpen_imp_P3 (X := X) (A := interior (closure (interior A))) h_open

theorem interior_closure_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure A)) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  simpa using
    Topology.isOpen_imp_P2 (X := X) (A := interior (closure A)) h_open

theorem interior_closure_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure A)) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  simpa using
    Topology.isOpen_imp_P1 (X := X) (A := interior (closure A)) h_open

theorem closure_interior_eq_closure_iff_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = closure A ↔ Topology.P1 A := by
  constructor
  · intro hEq
    dsimp [Topology.P1]
    have h : A ⊆ closure A := subset_closure
    simpa [hEq] using h
  · intro hP1
    exact Topology.P1_imp_closure_interior_eq_closure (X := X) (A := A) hP1

theorem P2_imp_interior_closure_interior_eq_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) :
    interior (closure (interior A)) = interior (closure A) := by
  have h_eq : closure (interior A) = closure A :=
    Topology.P2_imp_closure_interior_eq_closure (X := X) (A := A) hP2
  simpa [h_eq]

theorem P2_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) ↔ IsOpen (closure A) := by
  have h_closed : IsClosed (closure A) := isClosed_closure
  simpa using
    Topology.closed_P2_iff_isOpen (X := X) (A := closure A) h_closed

theorem interior_closure_interior_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure (interior A))) := by
  have h_open : IsOpen (interior (closure (interior A))) := isOpen_interior
  simpa using
    Topology.isOpen_imp_P2 (X := X) (A := interior (closure (interior A))) h_open

theorem closed_P3_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    interior A = A := by
  -- `closure A = A` since `A` is closed
  have h_cl : closure A = A := hA_closed.closure_eq
  -- From `P3`, we have `A ⊆ interior (closure A)`; rewrite using `h_cl`
  have h₁ : A ⊆ interior A := by
    dsimp [Topology.P3] at hP3
    simpa [h_cl] using hP3
  -- Always, `interior A ⊆ A`
  have h₂ : interior A ⊆ A := interior_subset
  -- Combine the two inclusions to get equality
  exact Set.Subset.antisymm h₂ h₁

theorem Topology.P2_nonempty_interiorClosureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) (hA : A.Nonempty) :
    (interior (closure (interior A))).Nonempty := by
  rcases hA with ⟨x, hx⟩
  exact ⟨x, hP2 hx⟩

theorem interior_closure_interior_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure (interior A))) := by
  have h_open : IsOpen (interior (closure (interior A))) := isOpen_interior
  simpa using
    Topology.isOpen_imp_P1 (X := X) (A := interior (closure (interior A))) h_open

theorem Topology.P1_nonempty_closureInterior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hA : A.Nonempty) :
    (closure (interior A)).Nonempty := by
  rcases hA with ⟨x, hx⟩
  exact ⟨x, hP1 hx⟩

theorem Topology.P2_nonempty_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hA : A.Nonempty) :
    (interior (closure A)).Nonempty := by
  -- First upgrade `P2` to `P3`
  have hP3 : Topology.P3 A :=
    Topology.P2_imp_P3 (X := X) (A := A) hP2
  -- Then use the existing result for `P3`
  exact Topology.P3_nonempty_interiorClosure (X := X) (A := A) hP3 hA

theorem P3_subset_interiorClosure_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP3 : Topology.P3 A) (hAB : A ⊆ B) :
    A ⊆ interior (closure B) := by
  dsimp [Topology.P3] at hP3
  have h_closure : closure A ⊆ closure B := closure_mono hAB
  have h_interior : interior (closure A) ⊆ interior (closure B) :=
    interior_mono h_closure
  exact Set.Subset.trans hP3 h_interior

theorem P3_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) :
    A ⊆ closure A := by
  dsimp [Topology.P3] at hP3
  exact Set.Subset.trans hP3 interior_subset

theorem P3_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 (closure A) := by
  intro hP3
  dsimp [Topology.P3] at hP3
  dsimp [Topology.P1]
  simpa using (closure_mono hP3)

theorem P2_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 (closure A) := by
  intro hP2
  have hP3 : Topology.P3 A :=
    Topology.P2_imp_P3 (X := X) (A := A) hP2
  exact Topology.P3_imp_P1_closure (X := X) (A := A) hP3

theorem isOpen_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_open : IsOpen A) :
    Topology.P1 (closure A) := by
  -- From openness we get `P2 A`
  have hP2 : Topology.P2 A :=
    Topology.isOpen_imp_P2 (X := X) (A := A) hA_open
  -- And `P2 A` implies `P1 (closure A)`
  exact Topology.P2_imp_P1_closure (X := X) (A := A) hP2

theorem Topology.P1_nonempty_interiorClosureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) (hA : A.Nonempty) :
    (interior (closure (interior A))).Nonempty := by
  classical
  -- First, show that `interior A` is non-empty.
  have hIntA : (interior A).Nonempty := by
    by_contra hIntEmpty
    have hIntEqEmpty : interior A = (∅ : Set X) :=
      Set.not_nonempty_iff_eq_empty.mp hIntEmpty
    have hClEmpty : closure (interior A) = (∅ : Set X) := by
      simpa [hIntEqEmpty, closure_empty] using
        (closure_empty : closure (∅ : Set X) = ∅)
    rcases hA with ⟨x, hxA⟩
    have hxCl : x ∈ closure (interior A) := hP1 hxA
    have : False := by
      simpa [hClEmpty] using hxCl
    exact this
  -- Pick a point of `interior A`.
  rcases hIntA with ⟨y, hyInt⟩
  -- `interior A` is contained in `interior (closure (interior A))`.
  have hSubset : interior A ⊆ interior (closure (interior A)) := by
    have : interior A ⊆ closure (interior A) := subset_closure
    have := interior_mono this
    simpa [interior_interior] using this
  exact ⟨y, hSubset hyInt⟩

theorem denseInterior_imp_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P2 A := by
  dsimp [Topology.P2]
  -- First, rewrite the target set using the density hypothesis.
  have h_int :
      interior (closure (interior A)) = (Set.univ : Set X) := by
    have : interior (closure (interior A)) =
        interior (Set.univ : Set X) := by
      simpa [h_dense]
    simpa [interior_univ] using this
  -- Now the inclusion `A ⊆ interior (closure (interior A))` is immediate.
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_int] using this

theorem P1_closure_iff_closureInterior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (closure A) ↔ closure (interior (closure A)) = closure A := by
  have h_closed : IsClosed (closure A) := isClosed_closure
  simpa using
    Topology.closed_P1_iff_closure_interior_eq (X := X) (A := closure A) h_closed

theorem P3_closure_iff_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) ↔ Topology.P2 (closure A) := by
  have h_closed : IsClosed (closure A) := isClosed_closure
  have h_equiv := Topology.closed_P2_iff_P3 (X := X) (A := closure A) h_closed
  simpa [h_equiv] using h_equiv.symm

theorem P1_iff_closure_subset_closureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A ↔ closure A ⊆ closure (interior A) := by
  constructor
  · intro hP1
    dsimp [Topology.P1] at hP1
    have h := closure_mono hP1
    simpa [closure_closure] using h
  · intro hClosure
    dsimp [Topology.P1]
    exact Set.Subset.trans subset_closure hClosure

theorem P2_subset_interiorClosure_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP2 : Topology.P2 A) (hAB : A ⊆ B) :
    A ⊆ interior (closure B) := by
  -- Upgrade `P2` to `P3`
  have hP3 : Topology.P3 A :=
    Topology.P2_imp_P3 (X := X) (A := A) hP2
  -- Use the existing lemma for `P3`
  exact
    Topology.P3_subset_interiorClosure_of_subset (X := X) (A := A) (B := B) hP3 hAB

theorem P1_subset_closure_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP1 : Topology.P1 A) (hAB : A ⊆ B) :
    A ⊆ closure B := by
  dsimp [Topology.P1] at hP1
  intro x hxA
  have hxClA : x ∈ closure (interior A) := hP1 hxA
  have h_cl_subset : closure (interior A) ⊆ closure (interior B) := by
    have h_int : interior A ⊆ interior B := interior_mono hAB
    exact closure_mono h_int
  have hxClIntB : x ∈ closure (interior B) := h_cl_subset hxClA
  have h_final : closure (interior B) ⊆ closure B := by
    have h_intB : interior B ⊆ B := interior_subset
    exact closure_mono h_intB
  exact h_final hxClIntB

theorem P1_imp_interior_closure_interior_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP1 : Topology.P1 A) :
    interior (closure (interior A)) = interior (closure A) := by
  have hEq : closure (interior A) = closure A :=
    Topology.P1_imp_closure_interior_eq_closure (X := X) (A := A) hP1
  simpa [hEq]

theorem P1_subset_closureInterior_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP1 : Topology.P1 A) (hAB : A ⊆ B) :
    A ⊆ closure (interior B) := by
  dsimp [Topology.P1] at hP1
  have h_closureInt : closure (interior A) ⊆ closure (interior B) := by
    have h_int : interior A ⊆ interior B := interior_mono hAB
    exact closure_mono h_int
  exact Set.Subset.trans hP1 h_closureInt

theorem denseInterior_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  -- First, show that `closure A = univ`.
  have h_closure_eq_univ : closure A = (Set.univ : Set X) := by
    -- `closure (interior A)` is contained in `closure A`, but it is `univ`.
    have h_subset : (Set.univ : Set X) ⊆ closure A := by
      simpa [h_dense] using
        (closure_mono (interior_subset : interior A ⊆ A))
    -- The reverse inclusion is trivial.
    exact Set.Subset.antisymm (Set.subset_univ _) h_subset
  -- Hence the interior of `closure A` is also all of `univ`.
  have h_int_eq_univ : interior (closure A) = (Set.univ : Set X) := by
    simpa [h_closure_eq_univ, interior_univ]
  -- Finally, establish the required inclusion.
  intro x hx
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_int_eq_univ] using this

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A) (hB : Topology.P1 B) :
    Topology.P1 (A ∪ B) := by
  dsimp [Topology.P1] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' := hA hxA
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        have hInt_subset : interior A ⊆ interior (A ∪ B) := by
          have h_sub : A ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono h_sub
        exact closure_mono hInt_subset
      exact h_subset hxA'
  | inr hxB =>
      have hxB' := hB hxB
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        have hInt_subset : interior B ⊆ interior (A ∪ B) := by
          have h_sub : B ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono h_sub
        exact closure_mono hInt_subset
      exact h_subset hxB'

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 A) (hB : Topology.P3 B) :
    Topology.P3 (A ∪ B) := by
  dsimp [Topology.P3] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' := hA hxA
      have h_subset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have h_closure : closure A ⊆ closure (A ∪ B) := by
          have h_sub : A ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact closure_mono h_sub
        exact interior_mono h_closure
      exact h_subset hxA'
  | inr hxB =>
      have hxB' := hB hxB
      have h_subset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have h_closure : closure B ⊆ closure (A ∪ B) := by
          have h_sub : B ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact closure_mono h_sub
        exact interior_mono h_closure
      exact h_subset hxB'

theorem P3_imp_closureInteriorClosure_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 A) :
    closure (interior (closure A)) = closure A := by
  -- First, upgrade `P3 A` to `P1 (closure A)`
  have hP1 : Topology.P1 (closure A) :=
    Topology.P3_imp_P1_closure (X := X) (A := A) hP3
  -- Use the equivalence between `P1 (closure A)` and the desired equality
  exact
    ((Topology.P1_closure_iff_closureInterior_eq_closure (X := X) (A := A)).1 hP1)

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 A) (hB : Topology.P2 B) :
    Topology.P2 (A ∪ B) := by
  dsimp [Topology.P2] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' := hA hxA
      have h_subset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) := by
        have h_int : interior A ⊆ interior (A ∪ B) := by
          have h_sub : A ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono h_sub
        have h_closure : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h_int
        exact interior_mono h_closure
      exact h_subset hxA'
  | inr hxB =>
      have hxB' := hB hxB
      have h_subset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) := by
        have h_int : interior B ⊆ interior (A ∪ B) := by
          have h_sub : B ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono h_sub
        have h_closure : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h_int
        exact interior_mono h_closure
      exact h_subset hxB'

theorem closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure (interior (closure A)) := by
  have h : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : A ⊆ closure A)
  exact closure_mono h

theorem interior_subset_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ interior (closure A) := by
  have h : A ⊆ closure A := subset_closure
  exact interior_mono h

theorem closureInterior_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior A)) := by
  have h_open : IsOpen (interior A) := isOpen_interior
  simpa using
    Topology.isOpen_imp_P1_closure (X := X) (A := interior A) h_open

theorem empty_P1_P2_P3 {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ∧ Topology.P2 (∅ : Set X) ∧ Topology.P3 (∅ : Set X) := by
  constructor
  · dsimp [Topology.P1]; simp
  · constructor
    · dsimp [Topology.P2]; simp
    · dsimp [Topology.P3]; simp

theorem P3_closure_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (closure A)) :
    IsOpen (closure A) := by
  have h_closed : IsClosed (closure A) := isClosed_closure
  exact
    Topology.closed_P3_isOpen (X := X) (A := closure A) h_closed hP3

theorem P1_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (closure A) := by
  intro hP1
  -- First, rewrite `P1 A` as an inclusion of closures.
  have h₁ : closure A ⊆ closure (interior A) :=
    (P1_iff_closure_subset_closureInterior (X := X) (A := A)).1 hP1
  -- Then, use the general inclusion `closure (interior A) ⊆ closure (interior (closure A))`.
  have h₂ : closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_interior_subset_closure_interior_closure (X := X) (A := A)
  -- Compose the two inclusions to obtain the desired result.
  dsimp [Topology.P1]
  exact Set.Subset.trans h₁ h₂

theorem closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply Set.Subset.antisymm
  · -- `closure (interior (closure (interior A))) ⊆ closure (interior A)`
    have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    have h₁' :
        closure (interior (closure (interior A))) ⊆
          closure (closure (interior A)) := closure_mono h₁
    simpa [closure_closure] using h₁'
  · -- `closure (interior A) ⊆ closure (interior (closure (interior A)))`
    have h₂ :
        closure (interior A) ⊆ closure (interior (closure (interior A))) := by
      have h :=
        closure_interior_subset_closure_interior_closure
          (X := X) (A := interior A)
      simpa [interior_interior] using h
    exact h₂

theorem interior_closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  have hInt : interior A ⊆ interior B := interior_mono hAB
  have hClos : closure (interior A) ⊆ closure (interior B) := closure_mono hInt
  exact interior_mono hClos

theorem P2_closureInterior_iff_isOpen_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  have h_closed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using
    Topology.closed_P2_iff_isOpen (X := X) (A := closure (interior A)) h_closed

theorem interior_univ_imp_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_int : interior A = (Set.univ : Set X)) :
    Topology.P2 A := by
  dsimp [Topology.P2]
  -- Compute `interior (closure (interior A))`
  have h_interior_closure :
      interior (closure (interior A)) = (Set.univ : Set X) := by
    have h_closure : closure (interior A) = (Set.univ : Set X) := by
      simpa [h_int, closure_univ]
    simpa [h_closure, interior_univ]
  -- The required inclusion is now trivial
  intro x hxA
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_interior_closure] using this

theorem univ_P1_P2_P3 {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ∧
      Topology.P2 (Set.univ : Set X) ∧
        Topology.P3 (Set.univ : Set X) := by
  constructor
  · dsimp [Topology.P1]; simp
  · constructor
    · dsimp [Topology.P2]; simp
    · dsimp [Topology.P3]; simp

theorem closure_interior_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) :
    closure (interior A) ⊆ closure (interior B) := by
  have hInt : interior A ⊆ interior B := interior_mono hAB
  exact closure_mono hInt

theorem P3_subset_interior_of_closure_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP3 : Topology.P3 A) (hcl : closure A ⊆ B) :
    A ⊆ interior B := by
  dsimp [Topology.P3] at hP3
  have hInt : interior (closure A) ⊆ interior B := interior_mono hcl
  exact Set.Subset.trans hP3 hInt

theorem P2_imp_closureInteriorClosure_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) :
    closure (interior (closure A)) = closure A := by
  -- First upgrade `P2 A` to `P3 A`.
  have hP3 : Topology.P3 A :=
    Topology.P2_imp_P3 (X := X) (A := A) hP2
  -- Then apply the existing result for `P3 A`.
  exact
    Topology.P3_imp_closureInteriorClosure_eq_closure (X := X) (A := A) hP3

theorem P3_closure_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (closure A)) :
    Topology.P3 A := by
  dsimp [Topology.P3] at hP3 ⊢
  intro x hxA
  have hxCl : (x : X) ∈ closure A := subset_closure hxA
  have hxInt : x ∈ interior (closure (closure A)) := hP3 hxCl
  simpa [closure_closure] using hxInt

theorem interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure A))) = interior (closure A) := by
  apply Set.Subset.antisymm
  ·
    have h :=
      interior_closure_interior_subset_interior_closure
        (X := X) (A := closure A)
    simpa using h
  ·
    have h_subset :
        interior (closure A) ⊆ closure (interior (closure A)) :=
      subset_closure
    have h := interior_mono h_subset
    simpa [interior_interior] using h

theorem P3_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) ↔ IsOpen (closure A) := by
  have h_closed : IsClosed (closure A) := isClosed_closure
  simpa using
    Topology.closed_P3_iff_isOpen (X := X) (A := closure A) h_closed

theorem closureInteriorClosure_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior (closure A))) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  simpa using
    Topology.isOpen_imp_P1_closure (X := X) (A := interior (closure A)) h_open

theorem P3_closureInterior_iff_isOpen_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  have h_closed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using
    Topology.closed_P3_iff_isOpen (X := X) (A := closure (interior A)) h_closed

theorem closure_eq_univ_of_denseInterior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    closure A = (Set.univ : Set X) := by
  apply Set.Subset.antisymm
  · exact Set.subset_univ _
  ·
    have h : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    simpa [h_dense] using h

theorem interior_closure_eq_univ_of_denseInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} (h_dense : closure (interior A) = (Set.univ : Set X)) :
    interior (closure A) = (Set.univ : Set X) := by
  -- First, obtain `closure A = univ` from the existing lemma.
  have h_closure : closure A = (Set.univ : Set X) :=
    closure_eq_univ_of_denseInterior (X := X) (A := A) h_dense
  -- Rewrite and conclude.
  calc
    interior (closure A)
        = interior (Set.univ : Set X) := by
          simpa [h_closure]
    _ = (Set.univ : Set X) := by
          simpa [interior_univ]

theorem closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure A)))) =
      closure (interior (closure A)) := by
  simpa using
    (closure_interior_closure_interior_eq (X := X) (A := closure A))

theorem interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  calc
    interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) := by
          simpa using
            (interior_closure_interior_closure_eq
              (X := X) (A := interior (closure A)))
    _ = interior (closure A) := by
          simpa using
            (interior_closure_interior_closure_eq
              (X := X) (A := A))

theorem P1_nonempty_iff_interior_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) :
    A.Nonempty ↔ (interior A).Nonempty := by
  classical
  constructor
  · intro hA
    by_contra hIntEmpty
    have hIntEq : interior A = (∅ : Set X) :=
      Set.not_nonempty_iff_eq_empty.mp hIntEmpty
    have hClInt : closure (interior A) = (∅ : Set X) := by
      simpa [hIntEq, closure_empty]
    rcases hA with ⟨x, hxA⟩
    have hxCl : x ∈ closure (interior A) := hP1 hxA
    simpa [hClInt] using hxCl
  · intro hInt
    exact hInt.mono interior_subset

theorem interior_P2_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior A) ↔ Topology.P3 (interior A) := by
  have h_open : IsOpen (interior A) := isOpen_interior
  simpa using
    Topology.isOpen_P2_iff_P3 (X := X) (A := interior A) h_open

theorem isOpen_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  have hP1 : Topology.P1 A :=
    Topology.isOpen_imp_P1 (X := X) (A := A) hA
  have hP2 : Topology.P2 A :=
    Topology.isOpen_imp_P2 (X := X) (A := A) hA
  have hP3 : Topology.P3 A :=
    Topology.isOpen_imp_P3 (X := X) (A := A) hA
  exact And.intro hP1 (And.intro hP2 hP3)

theorem closed_P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  have hA_open : IsOpen A :=
    Topology.closed_P2_isOpen (X := X) (A := A) hA_closed hP2
  exact Topology.isOpen_imp_P1 (X := X) (A := A) hA_open

theorem interior_closure_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (closure A)) = interior (closure A) := by
  simpa [closure_closure]

theorem closure_interior_closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior A))))) =
      closure (interior A) := by
  calc
    closure (interior (closure (interior (closure (interior A))))) =
        closure (interior (closure (interior A))) := by
          simpa using
            (closure_interior_closure_interior_eq
              (X := X) (A := closure (interior A)))
    _ = closure (interior A) := by
          simpa using
            (closure_interior_closure_interior_eq (X := X) (A := A))

theorem interior_closure_interior_closureInterior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior A)))) =
      interior (closure (interior A)) := by
  have h :=
    closure_interior_closure_interior_eq (X := X) (A := A)
  simpa [h]

theorem interior_closure_interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior A)))))) =
      interior (closure (interior A)) := by
  simpa using
    (interior_closure_interior_closure_interior_closure_eq
      (X := X) (A := interior A))

theorem closureInterior_inter_subset_inter_closureInterior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- `interior (A ∩ B)` is contained in both `interior A` and `interior B`
  have hA : interior (A ∩ B) ⊆ interior A := by
    have : A ∩ B ⊆ A := Set.inter_subset_left
    exact interior_mono this
  have hB : interior (A ∩ B) ⊆ interior B := by
    have : A ∩ B ⊆ B := Set.inter_subset_right
    exact interior_mono this
  -- Take closures to relate the membership of `x`
  have hxA : x ∈ closure (interior A) := (closure_mono hA) hx
  have hxB : x ∈ closure (interior B) := (closure_mono hB) hx
  exact And.intro hxA hxB

theorem P3_closure_closure_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (closure A)) ↔ Topology.P3 (closure A) := by
  dsimp [Topology.P3]
  simpa [closure_closure]

theorem closureInteriorClosureInterior_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior (closure (interior A)))) := by
  have h_open : IsOpen (interior (closure (interior A))) := isOpen_interior
  simpa using
    Topology.isOpen_imp_P1_closure (X := X)
      (A := interior (closure (interior A))) h_open

theorem P2_subset_interior_of_closure_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP2 : Topology.P2 A) (hcl : closure A ⊆ B) :
    A ⊆ interior B := by
  -- First, upgrade `P2 A` to `P3 A`.
  have hP3 : Topology.P3 A :=
    Topology.P2_imp_P3 (X := X) (A := A) hP2
  -- Now apply the existing lemma for `P3`.
  exact
    Topology.P3_subset_interior_of_closure_subset
      (X := X) (A := A) (B := B) hP3 hcl

theorem closureInterior_union_subset_closureInteriorUnion
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` lies in `closure (interior A)`
      -- We enlarge the set step by step:
      -- `interior A ⊆ interior (A ∪ B)`
      have hInt : interior A ⊆ interior (A ∪ B) := by
        have hSub : A ⊆ A ∪ B := by
          intro y hy; exact Or.inl hy
        exact interior_mono hSub
      -- Taking closures yields the desired containment.
      have hCl : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hInt
      exact hCl hxA
  | inr hxB =>
      -- Symmetric argument for `B`
      have hInt : interior B ⊆ interior (A ∪ B) := by
        have hSub : B ⊆ A ∪ B := by
          intro y hy; exact Or.inr hy
        exact interior_mono hSub
      have hCl : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hInt
      exact hCl hxB

theorem P1_subset_closureInterior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) :
    A ⊆ closure (interior (closure A)) := by
  have hSub : A ⊆ closure A := subset_closure
  exact
    P1_subset_closureInterior_of_subset (X := X) (A := A) (B := closure A) hP1 hSub

theorem P2_closure_closure_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (closure A)) ↔ Topology.P2 (closure A) := by
  dsimp [Topology.P2]
  simpa [closure_closure]

theorem P1_closure_closure_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (closure A)) ↔ Topology.P1 (closure A) := by
  dsimp [Topology.P1]
  simpa [closure_closure, interior_closure_closure_eq]

theorem interior_closure_P2_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure A)) ↔ Topology.P3 (interior (closure A)) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  simpa using
    Topology.isOpen_P2_iff_P3 (X := X) (A := interior (closure A)) h_open

theorem interior_closure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) :
    interior (closure A) ⊆ interior (closure B) := by
  exact interior_mono (closure_mono hAB)

theorem interior_P1_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior A) ↔ Topology.P3 (interior A) := by
  have h_open : IsOpen (interior A) := isOpen_interior
  simpa using
    Topology.isOpen_P1_iff_P3 (X := X) (A := interior A) h_open

theorem interior_univ_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_int : interior A = (Set.univ : Set X)) :
    Topology.P3 A := by
  -- From `interior A = univ`, we deduce `closure (interior A) = univ`.
  have h_dense : closure (interior A) = (Set.univ : Set X) := by
    simpa [h_int, closure_univ]
  -- Apply the existing lemma for dense interior.
  exact Topology.denseInterior_imp_P3 (X := X) (A := A) h_dense

theorem P2_closureInteriorClosure_iff_isOpen_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (closure A))) ↔
      IsOpen (closure (interior (closure A))) := by
  have h_closed : IsClosed (closure (interior (closure A))) := isClosed_closure
  simpa using
    Topology.closed_P2_iff_isOpen (X := X)
      (A := closure (interior (closure A))) h_closed

theorem closed_P3_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    Topology.P1 A := by
  -- First, a closed set satisfying `P3` is open.
  have hA_open : IsOpen A :=
    Topology.closed_P3_isOpen (X := X) (A := A) hA_closed hP3
  -- Openness implies `P1`.
  exact Topology.isOpen_imp_P1 (X := X) (A := A) hA_open

theorem denseInterior_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P1 (closure A) := by
  dsimp [Topology.P1]
  -- From the density of `interior A`, we have `closure A = univ`.
  have h_closure_univ : closure A = (Set.univ : Set X) :=
    closure_eq_univ_of_denseInterior (X := X) (A := A) h_dense
  -- Consequently, `closure (interior (closure A))` is also `univ`.
  have h_target : closure (interior (closure A)) = (Set.univ : Set X) := by
    have h_int : interior (closure A) = (Set.univ : Set X) := by
      simpa [h_closure_univ, interior_univ]
    have h' : closure (interior (closure A)) = closure (Set.univ : Set X) := by
      simpa [h_int]
    simpa [closure_univ] using h'
  -- Establish the required inclusion.
  intro x _hx
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_target] using this

theorem closure_interior_closure_interior_closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  -- First, collapse the two outermost layers.
  have h₁ :
      closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
        closure (interior (closure (interior (closure (interior A))))) := by
    simpa using
      (closure_interior_closure_interior_eq
        (X := X) (A := closure (interior (closure (interior A)))))
  -- Next, collapse the remaining three layers.
  have h₂ :
      closure (interior (closure (interior (closure (interior A))))) =
        closure (interior A) := by
    simpa using
      (closure_interior_closure_interior_closure_interior_eq
        (X := X) (A := A))
  -- Combine the two equalities.
  simpa using (h₁.trans h₂)



theorem P3_closureInteriorClosure_iff_isOpen_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior (closure A))) ↔
      IsOpen (closure (interior (closure A))) := by
  have h_closed : IsClosed (closure (interior (closure A))) := isClosed_closure
  simpa using
    Topology.closed_P3_iff_isOpen (X := X)
      (A := closure (interior (closure A))) h_closed

theorem closure_interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure A := by
  have h : interior A ⊆ A := interior_subset
  exact closure_mono h

theorem interior_P1_iff_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior A) ↔ Topology.P2 (interior A) := by
  have h_open : IsOpen (interior A) := isOpen_interior
  simpa using
    Topology.isOpen_P1_iff_P2 (X := X) (A := interior A) h_open

theorem interior_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure A := by
  exact
    Set.Subset.trans
      (interior_closure_interior_subset_interior_closure (X := X) (A := A))
      interior_subset

theorem isClosed_of_closureInterior_eq {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : closure (interior A) = A) :
    IsClosed A := by
  have : IsClosed (closure (interior A)) := isClosed_closure
  simpa [h] using this

theorem isOpen_closure_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure A)) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hxA
  have hxCl : x ∈ closure A := subset_closure hxA
  have hInt : interior (closure A) = closure A := h_open.interior_eq
  simpa [hInt] using hxCl

theorem closureInterior_subset_closureInterior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ⊆ closure (interior (A ∪ B)) := by
  have hInt : interior A ⊆ interior (A ∪ B) := by
    have hSub : A ⊆ A ∪ B := by
      intro x hx; exact Or.inl hx
    exact interior_mono hSub
  exact closure_mono hInt



theorem denseInterior_imp_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P3 (closure A) := by
  -- We will show that `interior (closure A) = univ`, which makes `P3` trivial.
  have hIntUniv : interior (closure A) = (Set.univ : Set X) :=
    interior_closure_eq_univ_of_denseInterior (X := X) (A := A) h_dense
  -- Unfold `P3` for the set `closure A`.
  dsimp [Topology.P3]
  intro x hx
  -- Every point belongs to `univ`, and hence to `interior (closure A)`.
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [hIntUniv] using this

theorem interior_closure_interior_closure_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (closure (interior (closure A)))) := by
  have h_open : IsOpen (interior (closure (interior (closure A)))) :=
    isOpen_interior
  simpa using
    Topology.isOpen_imp_P3 (X := X)
      (A := interior (closure (interior (closure A)))) h_open

theorem interior_closure_interior_closure_interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior (closure A))))))) =
      interior (closure A) := by
  have h :=
    interior_closure_interior_closure_interior_closure_interior_closure_eq
      (X := X) (A := closure A)
  simpa [closure_closure] using h

theorem closure_interior_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (interior A)) = closure (interior A) := by
  simpa [interior_interior]

theorem interior_subset_interiorClosureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ interior (closure (interior A)) := by
  -- First, `interior A` is contained in `closure (interior A)`.
  have h₁ : interior A ⊆ closure (interior A) := subset_closure
  -- Applying `interior` to both sides (and using monotonicity) yields the result.
  have h₂ : interior (interior A) ⊆ interior (closure (interior A)) :=
    interior_mono h₁
  simpa [interior_interior] using h₂

theorem closed_P2_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) :
    interior A = A := by
  have hA_open : IsOpen A :=
    Topology.closed_P2_isOpen (X := X) (A := A) hA_closed hP2
  simpa using hA_open.interior_eq

theorem P3_imp_eq_empty_of_interiorClosure_empty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A)
    (hInt : interior (closure A) = (∅ : Set X)) :
    A = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hxA
    have : (x : X) ∈ interior (closure A) := hP3 hxA
    simpa [hInt] using this
  · exact Set.empty_subset _

theorem P3_nonempty_iff_interiorClosure_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 A) :
    A.Nonempty ↔ (interior (closure A)).Nonempty := by
  constructor
  · intro hA
    exact
      Topology.P3_nonempty_interiorClosure (X := X) (A := A) hP3 hA
  · intro hInt
    rcases hInt with ⟨x, hxInt⟩
    -- From `hxInt : x ∈ interior (closure A)` we know `x ∈ closure A`.
    have hxCl : x ∈ closure A := interior_subset hxInt
    -- Use the characterization of points in the closure of `A`.
    have hIntersect :
        ((interior (closure A)) ∩ A).Nonempty := by
      have hMemClosure := (mem_closure_iff).1 hxCl
      simpa using hMemClosure (interior (closure A)) isOpen_interior hxInt
    -- Extract a witness from the non-empty intersection.
    rcases hIntersect with ⟨y, _, hyA⟩
    exact ⟨y, hyA⟩

theorem interior_closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior A)))) =
      interior (closure (interior A)) := by
  have h :=
    (closure_interior_closure_interior_eq (X := X) (A := A))
  simpa [h]

theorem interior_closure_inter_subset_interior_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hA : x ∈ interior (closure A) := by
    have h_subset : interior (closure (A ∩ B)) ⊆ interior (closure A) := by
      have h_closure : closure (A ∩ B) ⊆ closure A :=
        closure_mono (Set.inter_subset_left)
      exact interior_mono h_closure
    exact h_subset hx
  have hB : x ∈ interior (closure B) := by
    have h_subset : interior (closure (A ∩ B)) ⊆ interior (closure B) := by
      have h_closure : closure (A ∩ B) ⊆ closure B :=
        closure_mono (Set.inter_subset_right)
      exact interior_mono h_closure
    exact h_subset hx
  exact And.intro hA hB

theorem interior_closure_union_subset_interior_closureUnion
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- Handle the case `x ∈ interior (closure A)`
      -- Since `closure A ⊆ closure (A ∪ B)`, taking interiors yields the desired inclusion.
      have h_closure : closure A ⊆ closure (A ∪ B) := by
        have h_sub : A ⊆ A ∪ B := by
          intro y hy; exact Or.inl hy
        exact closure_mono h_sub
      have h_interior : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_closure
      exact h_interior hxA
  | inr hxB =>
      -- Symmetric argument for `x ∈ interior (closure B)`
      have h_closure : closure B ⊆ closure (A ∪ B) := by
        have h_sub : B ⊆ A ∪ B := by
          intro y hy; exact Or.inr hy
        exact closure_mono h_sub
      have h_interior : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_closure
      exact h_interior hxB

theorem P2_imp_eq_empty_of_closureInterior_empty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A)
    (hClInt : closure (interior A) = (∅ : Set X)) :
    A = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hxA
    have hx₁ : x ∈ interior (closure (interior A)) := hP2 hxA
    have hx₂ : x ∈ closure (interior A) :=
      (interior_subset : interior (closure (interior A)) ⊆
        closure (interior A)) hx₁
    simpa [hClInt] using hx₂
  · exact Set.empty_subset _

theorem interior_closure_eq_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    interior (closure A) = interior A := by
  simpa [hA.closure_eq]

theorem Topology.P2_nonempty_closureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) (hA : A.Nonempty) :
    (closure (interior A)).Nonempty := by
  have hP1 : Topology.P1 A :=
    Topology.P2_imp_P1 (X := X) (A := A) hP2
  exact Topology.P1_nonempty_closureInterior (X := X) (A := A) hP1 hA

theorem denseInterior_imp_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P2 (closure A) := by
  dsimp [Topology.P2]
  -- First, note that `closure A = univ`.
  have h_closure : closure A = (Set.univ : Set X) :=
    closure_eq_univ_of_denseInterior (X := X) (A := A) h_dense
  -- Next, compute `interior (closure (interior (closure A))) = univ`.
  have h_target :
      interior (closure (interior (closure A))) = (Set.univ : Set X) := by
    -- `interior (closure A)` is already `univ`.
    have h_int : interior (closure A) = (Set.univ : Set X) := by
      simpa [h_closure, interior_univ]
    -- Hence its closure is also `univ`.
    have h_cl : closure (interior (closure A)) = (Set.univ : Set X) := by
      simpa [h_int, closure_univ]
    -- Taking the interior once more yields `univ`.
    simpa [h_cl, interior_univ] using rfl
  -- Establish the required inclusion.
  intro x _hx
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_closure, h_target] using this

theorem P1_imp_eq_empty_of_closureInterior_empty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A)
    (hClInt : closure (interior A) = (∅ : Set X)) :
    A = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hxA
    have hxCl : (x : X) ∈ closure (interior A) := hP1 hxA
    simpa [hClInt] using hxCl
  · exact Set.empty_subset _

theorem closureInteriorClosureInteriorClosureInterior_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior (closure (interior (closure (interior A)))))) := by
  have h_open :
      IsOpen (interior (closure (interior (closure (interior A))))) :=
    isOpen_interior
  simpa using
    Topology.isOpen_imp_P1_closure (X := X)
      (A := interior (closure (interior (closure (interior A))))) h_open

theorem P1_imp_eq_empty_of_interior_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) (hInt : interior A = (∅ : Set X)) :
    A = (∅ : Set X) := by
  -- From `hInt` we immediately deduce that `closure (interior A)` is empty.
  have hClInt : closure (interior A) = (∅ : Set X) := by
    simpa [hInt, closure_empty]
  -- Apply the existing lemma formulated in terms of the closure of the interior.
  exact
    P1_imp_eq_empty_of_closureInterior_empty (X := X) (A := A) hP1 hClInt

theorem denseInterior_imp_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  have hP1 : Topology.P1 A :=
    Topology.denseInterior_imp_P1 (X := X) (A := A) h_dense
  have hP2 : Topology.P2 A :=
    Topology.denseInterior_imp_P2 (X := X) (A := A) h_dense
  have hP3 : Topology.P3 A :=
    Topology.denseInterior_imp_P3 (X := X) (A := A) h_dense
  exact And.intro hP1 (And.intro hP2 hP3)

theorem closure_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure A)) ⊆ closure A := by
  -- We start with the basic inclusion `interior (closure A) ⊆ closure A`.
  have h : interior (closure A) ⊆ closure A := interior_subset
  -- Applying `closure_mono` to this inclusion yields the desired result.
  simpa [closure_closure] using (closure_mono h)

theorem interior_closure_subset_interior_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ⊆ interior (closure (A ∪ B)) := by
  have h_closure : closure A ⊆ closure (A ∪ B) := by
    have h_subset : A ⊆ A ∪ B := by
      intro x hx
      exact Or.inl hx
    exact closure_mono h_subset
  exact interior_mono h_closure

theorem P2_imp_closure_subset_closureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) :
    closure A ⊆ closure (interior A) := by
  -- First, upgrade `P2 A` to `P1 A`.
  have hP1 : Topology.P1 A :=
    Topology.P2_imp_P1 (X := X) (A := A) hP2
  -- Translate `P1 A` into the desired inclusion of closures.
  exact
    (Topology.P1_iff_closure_subset_closureInterior (X := X) (A := A)).1 hP1

theorem P2_nonempty_iff_interior_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) :
    A.Nonempty ↔ (interior A).Nonempty := by
  classical
  constructor
  · intro hA
    rcases hA with ⟨x, hxA⟩
    have hxIntCl : x ∈ interior (closure (interior A)) := hP2 hxA
    by_cases hInt : (interior A).Nonempty
    · exact hInt
    · -- If `interior A` were empty, we would derive a contradiction.
      have hIntEq : interior A = (∅ : Set X) :=
        Set.not_nonempty_iff_eq_empty.1 hInt
      have hClIntEq : closure (interior A) = (∅ : Set X) := by
        simpa [hIntEq, closure_empty]
      have hIntClEq : interior (closure (interior A)) = (∅ : Set X) := by
        simpa [hClIntEq, interior_empty]
      have hFalse : False := by
        simpa [hIntClEq] using hxIntCl
      exact False.elim hFalse
  · intro hInt
    exact hInt.mono interior_subset

theorem closureInterior_union_eq_union_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∪ B)) = closure A ∪ closure B := by
  -- `interior` of an open set is itself.
  have h_int : interior (A ∪ B) = A ∪ B := by
    have h_open : IsOpen (A ∪ B) := hA.union hB
    simpa using h_open.interior_eq
  -- Rewrite and use the distributivity of `closure` over unions.
  calc
    closure (interior (A ∪ B)) = closure (A ∪ B) := by
      simpa [h_int]
    _ = closure A ∪ closure B := by
      simpa using
        (closure_union : closure (A ∪ B) = closure A ∪ closure B)

theorem P2_closureInterior_iff_P3_closureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 (closure (interior A)) ↔ Topology.P3 (closure (interior A)) := by
  have h_closed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using
    Topology.closed_P2_iff_P3 (X := X) (A := closure (interior A)) h_closed

theorem P2_closure_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (closure A)) :
    Topology.P3 A := by
  -- First, convert `P2 (closure A)` into `P3 (closure A)` using the closed‐set equivalence.
  have hP3_closure : Topology.P3 (closure A) :=
    (Topology.P3_closure_iff_P2_closure (X := X) (A := A)).mpr hP2
  -- Then, propagate `P3` from `closure A` back to `A`.
  exact Topology.P3_closure_imp_P3 (X := X) (A := A) hP3_closure

theorem closure_interior_closure_interior_closureClosure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure A)))) =
      closure (interior (closure A)) := by
  simpa using
    (closure_interior_closure_interior_eq (X := X) (A := closure A))

theorem P1_imp_closureInteriorClosure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    closure (interior (closure A)) = closure A := by
  -- First, upgrade `P1 A` to `P1 (closure A)`.
  have hP1_cl : Topology.P1 (closure A) :=
    Topology.P1_imp_P1_closure (X := X) (A := A) hP1
  -- Use the established equivalence for `closure A`.
  exact
    ((Topology.P1_closure_iff_closureInterior_eq_closure (X := X) (A := A)).1
      hP1_cl)

theorem closure_interior_closure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) :
    closure (interior (closure A)) ⊆ closure (interior (closure B)) := by
  have hInt : interior (closure A) ⊆ interior (closure B) :=
    interior_closure_mono (X := X) (A := A) (B := B) hAB
  exact closure_mono hInt

theorem interior_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior A) ∧ Topology.P2 (interior A) ∧ Topology.P3 (interior A) := by
  have h_open : IsOpen (interior A) := isOpen_interior
  simpa using
    Topology.isOpen_P1_P2_P3 (X := X) (A := interior A) h_open

theorem closure_subset_closureInterior_of_subset_P1 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hP1B : Topology.P1 B) :
    closure A ⊆ closure (interior B) := by
  -- First, use monotonicity of `closure` to enlarge from `A` to `B`.
  have h₁ : closure A ⊆ closure B := closure_mono hAB
  -- Unfold the definition of `P1` for `B`.
  dsimp [Topology.P1] at hP1B
  -- Since `closure (interior B)` is closed and contains `B`,
  -- minimality of the closure yields the desired inclusion.
  have h₂ : closure B ⊆ closure (interior B) :=
    closure_minimal hP1B isClosed_closure
  -- Combine the two inclusions.
  exact Set.Subset.trans h₁ h₂

theorem isOpen_closure_of_denseInterior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    IsOpen (closure A) := by
  -- From the density of the interior we obtain `P3 (closure A)`.
  have hP3 : Topology.P3 (closure A) :=
    denseInterior_imp_P3_closure (X := X) (A := A) h_dense
  -- A set satisfying `P3` and being closed is open.
  exact P3_closure_isOpen_closure (X := X) (A := A) hP3

theorem closed_P3_imp_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    Topology.P2 A := by
  have h_eq : Topology.P2 A ↔ Topology.P3 A :=
    Topology.closed_P2_iff_P3 (X := X) (A := A) hA_closed
  exact (h_eq.mpr hP3)

theorem closureInteriorClosureInterior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) ⊆ closure A := by
  -- We already have `interior (closure (interior A)) ⊆ closure A`.
  have h :
      interior (closure (interior A)) ⊆ closure A :=
    interior_closure_interior_subset_closure (X := X) (A := A)
  -- Taking closures preserves inclusions.
  simpa [closure_closure] using closure_mono h

theorem interior_nonempty_iff_interiorClosureInterior_nonempty {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    (interior A).Nonempty ↔ (interior (closure (interior A))).Nonempty := by
  classical
  constructor
  · intro hIntA
    rcases hIntA with ⟨x, hx⟩
    have hSub : interior A ⊆ interior (closure (interior A)) := by
      have h₁ : interior A ⊆ closure (interior A) := subset_closure
      have h₂ := interior_mono h₁
      simpa [interior_interior] using h₂
    exact ⟨x, hSub hx⟩
  · intro hIntCl
    by_cases hIntA : (interior A).Nonempty
    · exact hIntA
    ·
      have hIntAEq : interior A = (∅ : Set X) :=
        (Set.not_nonempty_iff_eq_empty).1 hIntA
      have hIntClEq : interior (closure (interior A)) = (∅ : Set X) := by
        simpa [hIntAEq, closure_empty, interior_empty]
      rcases hIntCl with ⟨x, hx⟩
      have hFalse : False := by
        have : (x : X) ∈ (∅ : Set X) := by
          simpa [hIntClEq] using hx
        exact this
      exact (False.elim hFalse)

theorem isOpen_closure_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure A)) :
    Topology.P1 (closure A) := by
  simpa using
    Topology.isOpen_imp_P1 (X := X) (A := closure A) h_open

theorem closed_P3_imp_closureInterior_eq {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    closure (interior A) = A := by
  -- First, use the existing lemma to get `interior A = A`.
  have hInt : interior A = A :=
    closed_P3_interior_eq (X := X) (A := A) hA_closed hP3
  -- Rewrite and use that `A` is closed, so `closure A = A`.
  simpa [hInt, hA_closed.closure_eq]

theorem isOpen_closure_imp_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure A)) :
    Topology.P2 (closure A) := by
  simpa using
    Topology.isOpen_imp_P2 (X := X) (A := closure A) h_open

theorem isOpen_closure_imp_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure A)) :
    Topology.P3 (closure A) := by
  simpa using Topology.isOpen_imp_P3 (X := X) (A := closure A) h_open



theorem interior_closure_interior_closure_P2 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 (interior (closure (interior (closure A)))) := by
  have h_open : IsOpen (interior (closure (interior (closure A)))) := isOpen_interior
  simpa using
    Topology.isOpen_imp_P2 (X := X)
      (A := interior (closure (interior (closure A)))) h_open

theorem interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure A := by
  intro x hx
  have hxA : (x : X) ∈ A := interior_subset hx
  exact subset_closure hxA

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → Topology.P1 A) :
    Topology.P1 (⋃₀ 𝒜) := by
  dsimp [Topology.P1]
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hA_mem, hxA⟩
  have hP1A := h𝒜 A hA_mem
  have hxClA : x ∈ closure (interior A) := hP1A hxA
  have hInt_subset : interior A ⊆ interior (⋃₀ 𝒜) := by
    have hSub : A ⊆ ⋃₀ 𝒜 := Set.subset_sUnion_of_mem hA_mem
    exact interior_mono hSub
  have hCl_subset : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono hInt_subset
  exact hCl_subset hxClA

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → Topology.P3 A) :
    Topology.P3 (⋃₀ 𝒜) := by
  dsimp [Topology.P3]
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hA_mem, hxA⟩
  have hP3A := h𝒜 A hA_mem
  have hxIntA : x ∈ interior (closure A) := hP3A hxA
  have h_closure : closure A ⊆ closure (⋃₀ 𝒜) := by
    have h_sub : A ⊆ ⋃₀ 𝒜 := Set.subset_sUnion_of_mem hA_mem
    exact closure_mono h_sub
  have h_interior :
      interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) :=
    interior_mono h_closure
  exact h_interior hxIntA

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → Topology.P2 A) :
    Topology.P2 (⋃₀ 𝒜) := by
  dsimp [Topology.P2]
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hA_mem, hxA⟩
  have hP2A := h𝒜 A hA_mem
  have hxIntClA : x ∈ interior (closure (interior A)) := hP2A hxA
  have h_inclusion :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) := by
    -- `interior A` is contained in `interior (⋃₀ 𝒜)`
    have h_int_subset : interior A ⊆ interior (⋃₀ 𝒜) := by
      have h_subset : A ⊆ ⋃₀ 𝒜 := Set.subset_sUnion_of_mem hA_mem
      exact interior_mono h_subset
    -- Taking closures preserves inclusions
    have h_closure_subset :
        closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
      closure_mono h_int_subset
    -- And interiors are monotone
    exact interior_mono h_closure_subset
  exact h_inclusion hxIntClA

theorem interior_eq_self_imp_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_int : interior A = A) :
    Topology.P2 A := by
  -- From `interior A = A`, we deduce that `A` is open.
  have hOpen : IsOpen A := by
    simpa [h_int] using (isOpen_interior : IsOpen (interior A))
  -- Openness immediately yields `P2`.
  exact Topology.isOpen_imp_P2 (X := X) (A := A) hOpen

theorem P1_iUnion {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, Topology.P1 (A i)) :
    Topology.P1 (⋃ i, A i) := by
  classical
  dsimp [Topology.P1] at hA ⊢
  intro x hxUnion
  rcases Set.mem_iUnion.mp hxUnion with ⟨i, hxAi⟩
  have hxClAi : x ∈ closure (interior (A i)) := (hA i) hxAi
  have hInt_subset : interior (A i) ⊆ interior (⋃ i, A i) := by
    have hSub : A i ⊆ ⋃ j, A j := Set.subset_iUnion _ _
    exact interior_mono hSub
  have hCl_subset :
      closure (interior (A i)) ⊆ closure (interior (⋃ i, A i)) :=
    closure_mono hInt_subset
  exact hCl_subset hxClAi

theorem closure_interior_subset_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) :
    closure (interior A) ⊆ A := by
  -- `interior A` is contained in `A`
  have hInt : interior A ⊆ A := interior_subset
  -- Taking closures preserves inclusions
  have hClos : closure (interior A) ⊆ closure A := closure_mono hInt
  -- Since `A` is closed, `closure A = A`
  simpa [hA_closed.closure_eq] using hClos

theorem P2_iUnion {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, Topology.P2 (A i)) :
    Topology.P2 (⋃ i, A i) := by
  dsimp [Topology.P2] at hA ⊢
  intro x hxUnion
  rcases Set.mem_iUnion.mp hxUnion with ⟨i, hxAi⟩
  -- Apply `P2` to obtain membership in the appropriate interior.
  have hxP2 : x ∈ interior (closure (interior (A i))) := (hA i) hxAi
  -- Relate the successive interiors and closures for `A i` and the union.
  have h_int_subset : interior (A i) ⊆ interior (⋃ j, A j) := by
    have h_sub : A i ⊆ ⋃ j, A j := Set.subset_iUnion _ _
    exact interior_mono h_sub
  have h_closure_subset :
      closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) :=
    closure_mono h_int_subset
  have h_interior_subset :
      interior (closure (interior (A i))) ⊆
        interior (closure (interior (⋃ j, A j))) :=
    interior_mono h_closure_subset
  exact h_interior_subset hxP2

theorem P3_iUnion {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, Topology.P3 (A i)) :
    Topology.P3 (⋃ i, A i) := by
  dsimp [Topology.P3] at hA ⊢
  intro x hxUnion
  rcases Set.mem_iUnion.mp hxUnion with ⟨i, hxAi⟩
  have hxIntA : x ∈ interior (closure (A i)) := (hA i) hxAi
  have h_closure_subset : closure (A i) ⊆ closure (⋃ j, A j) := by
    have h_sub : A i ⊆ ⋃ j, A j := Set.subset_iUnion _ _
    exact closure_mono h_sub
  have h_interior_subset :
      interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) :=
    interior_mono h_closure_subset
  exact h_interior_subset hxIntA

theorem P2_nonempty_iff_interiorClosure_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) :
    A.Nonempty ↔ (interior (closure A)).Nonempty := by
  classical
  constructor
  · intro hA
    exact
      Topology.P2_nonempty_interiorClosure (X := X) (A := A) hP2 hA
  · intro hInt
    by_cases hA : A.Nonempty
    · exact hA
    · -- Derive a contradiction from `hInt`
      have hA_eq : A = (∅ : Set X) :=
        (Set.not_nonempty_iff_eq_empty).1 hA
      have hIntEq : interior (closure A) = (∅ : Set X) := by
        simpa [hA_eq, closure_empty, interior_empty]
      rcases hInt with ⟨x, hx⟩
      have hFalse : False := by
        have : (x : X) ∈ (∅ : Set X) := by
          simpa [hIntEq] using hx
        simpa using this
      exact False.elim hFalse

theorem P2_imp_eq_empty_of_interior_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) (hInt : interior A = (∅ : Set X)) :
    A = (∅ : Set X) := by
  -- From `interior A = ∅`, deduce `closure (interior A) = ∅`.
  have hClInt : closure (interior A) = (∅ : Set X) := by
    simpa [hInt] using (closure_empty : closure (∅ : Set X) = ∅)
  -- Apply the existing lemma formulated in terms of `closure (interior A)`.
  exact
    P2_imp_eq_empty_of_closureInterior_empty (X := X) (A := A) hP2 hClInt

theorem interior_union {α : Type*} [TopologicalSpace α] (A B : Set α) :
    interior (A ∪ B) = interior (A ∪ B) := rfl

theorem closure_interior_closure_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (closure A))) =
      closure (interior (closure A)) := by
  simp [closure_closure, interior_closure_closure_eq]

theorem P1_interior_interior_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (interior A)) ↔ Topology.P1 (interior A) := by
  simpa [interior_interior]

theorem interior_eq_self_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_int : interior A = A) :
    Topology.P1 A := by
  -- The equality `interior A = A` shows that `A` is open.
  have hOpen : IsOpen A := by
    simpa [h_int] using (isOpen_interior : IsOpen (interior A))
  -- Openness of `A` implies `P1 A`.
  simpa using Topology.isOpen_imp_P1 (X := X) (A := A) hOpen

theorem closed_P2_imp_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) :
    IsOpen A ∧ IsClosed A := by
  -- From `hP2` and the fact that `A` is closed, we know that `A` is open.
  have h_open : IsOpen A :=
    Topology.closed_P2_isOpen (X := X) (A := A) hA_closed hP2
  -- Combine the obtained openness with the given closedness.
  exact And.intro h_open hA_closed

theorem closureInterior_inter_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆ closure A ∩ closure B := by
  -- First, use the existing inclusion into the intersection of
  -- the closures of the interiors.
  have h₁ :
      closure (interior (A ∩ B)) ⊆
        closure (interior A) ∩ closure (interior B) :=
    closureInterior_inter_subset_inter_closureInterior
      (X := X) (A := A) (B := B)
  -- Next, observe that each `closure (interior _)` is contained in the corresponding `closure _`.
  have h₂ :
      (closure (interior A) ∩ closure (interior B)) ⊆
        closure A ∩ closure B := by
    intro x hx
    rcases hx with ⟨hxA, hxB⟩
    exact And.intro
      (closure_interior_subset_closure (X := X) (A := A) hxA)
      (closure_interior_subset_closure (X := X) (A := B) hxB)
  -- Combine the two inclusions.
  exact Set.Subset.trans h₁ h₂

theorem interior_closure_subset_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ⊆ closure (interior (closure A)) := by
  simpa using
    (subset_closure :
      interior (closure A) ⊆ closure (interior (closure A)))

theorem isOpen_inter_imp_P2 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P2 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B) := IsOpen.inter hA hB
  simpa using
    Topology.isOpen_imp_P2 (X := X) (A := A ∩ B) hOpen

theorem closureInterior_union_subset_union_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (A ∪ B)) ⊆ closure A ∪ closure B := by
  -- `interior (A ∪ B)` is contained in `A ∪ B`.
  have h_subset : interior (A ∪ B) ⊆ A ∪ B := interior_subset
  -- Taking closures preserves inclusions.
  have h_closure : closure (interior (A ∪ B)) ⊆ closure (A ∪ B) :=
    closure_mono h_subset
  -- Express `closure (A ∪ B)` as the union of the closures of `A` and `B`.
  simpa [closure_union] using h_closure

theorem closureInterior_union_eq_union_closureInterior_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∪ B)) = closure (interior A) ∪ closure (interior B) := by
  -- Since `A` and `B` are open, so is their union, and the `interior`
  -- of an open set is itself.
  have h_union_open : IsOpen (A ∪ B) := hA.union hB
  simpa [h_union_open.interior_eq, hA.interior_eq, hB.interior_eq] using
    (closure_union : closure (A ∪ B) = closure A ∪ closure B)

theorem interior_closure_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure A)) ∧
      Topology.P2 (interior (closure A)) ∧
        Topology.P3 (interior (closure A)) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  simpa using
    Topology.isOpen_P1_P2_P3 (X := X) (A := interior (closure A)) h_open

theorem interior_closure_interior_subset_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior (closure A)) := by
  -- First, `interior (closure (interior A)) ⊆ interior (closure A)`.
  have h₁ :
      interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_closure_interior_subset_interior_closure (X := X) (A := A)
  -- Second, `interior (closure A) ⊆ closure (interior (closure A))`.
  have h₂ :
      interior (closure A) ⊆ closure (interior (closure A)) :=
    interior_closure_subset_closureInteriorClosure (X := X) (A := A)
  -- Composing the two inclusions yields the desired result.
  exact Set.Subset.trans h₁ h₂

theorem P1_subset_closureInteriorClosureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) :
    A ⊆ closure (interior (closure (interior A))) := by
  -- Expand the definition of `P1` to obtain the starting inclusion.
  dsimp [Topology.P1] at hP1
  intro x hxA
  have hxClInt : x ∈ closure (interior A) := hP1 hxA
  -- Use monotonicity to enlarge the ambient set.
  have h_subset :
      closure (interior A) ⊆ closure (interior (closure (interior A))) := by
    simpa [interior_interior] using
      closure_interior_subset_closure_interior_closure
        (X := X) (A := interior A)
  exact h_subset hxClInt

theorem closed_P3_inter {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B)
    (hP3A : Topology.P3 A) (hP3B : Topology.P3 B) :
    Topology.P3 (A ∩ B) := by
  -- Both `A` and `B` are closed and satisfy `P3`, hence they are open.
  have hOpenA : IsOpen A :=
    Topology.closed_P3_isOpen (X := X) (A := A) hA_closed hP3A
  have hOpenB : IsOpen B :=
    Topology.closed_P3_isOpen (X := X) (A := B) hB_closed hP3B
  -- The intersection of two open sets is open.
  have hOpenInter : IsOpen (A ∩ B) := IsOpen.inter hOpenA hOpenB
  -- Openness implies `P3`.
  simpa using
    Topology.isOpen_imp_P3 (X := X) (A := A ∩ B) hOpenInter

theorem interior_closure_interior_interior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (interior A))) =
      interior (closure (interior A)) := by
  simpa [interior_interior]

theorem P3_imp_closure_subset_closureInteriorClosure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 A) :
    closure A ⊆ closure (interior (closure A)) := by
  -- First, upgrade `P3 A` to `P1 (closure A)`.
  have hP1 : Topology.P1 (closure A) :=
    Topology.P3_imp_P1_closure (X := X) (A := A) hP3
  -- Unfold the definition of `P1` for `closure A` and use it directly.
  dsimp [Topology.P1] at hP1
  simpa using hP1

theorem interior_closure_eq_univ_iff_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) = (Set.univ : Set X) ↔
      closure A = (Set.univ : Set X) := by
  constructor
  · intro hInt
    have h_subset : (Set.univ : Set X) ⊆ closure A := by
      have h_sub : interior (closure A) ⊆ closure A := interior_subset
      simpa [hInt] using h_sub
    exact Set.Subset.antisymm (Set.subset_univ _) h_subset
  · intro hCl
    have : interior (closure A) = interior (Set.univ : Set X) := by
      simpa [hCl]
    simpa [interior_univ] using this

theorem denseInterior_imp_P1_P2_P3_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P1 (closure A) ∧ Topology.P2 (closure A) ∧ Topology.P3 (closure A) := by
  have hP1 : Topology.P1 (closure A) :=
    denseInterior_imp_P1_closure (X := X) (A := A) h_dense
  have hP2 : Topology.P2 (closure A) :=
    denseInterior_imp_P2_closure (X := X) (A := A) h_dense
  have hP3 : Topology.P3 (closure A) :=
    denseInterior_imp_P3_closure (X := X) (A := A) h_dense
  exact And.intro hP1 (And.intro hP2 hP3)

theorem isOpen_inter_imp_P1 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P1 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B) := IsOpen.inter hA hB
  simpa using Topology.isOpen_imp_P1 (X := X) (A := A ∩ B) hOpen

theorem isOpen_closure_imp_P1_P2_P3_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (h_open : IsOpen (closure A)) :
    Topology.P1 (closure A) ∧ Topology.P2 (closure A) ∧ Topology.P3 (closure A) := by
  have hP1 : Topology.P1 (closure A) :=
    isOpen_closure_imp_P1 (X := X) (A := A) h_open
  have hP2 : Topology.P2 (closure A) :=
    isOpen_closure_imp_P2_closure (X := X) (A := A) h_open
  have hP3 : Topology.P3 (closure A) :=
    isOpen_closure_imp_P3_closure (X := X) (A := A) h_open
  exact And.intro hP1 (And.intro hP2 hP3)

theorem closed_P2_inter {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B)
    (hP2A : Topology.P2 A) (hP2B : Topology.P2 B) :
    Topology.P2 (A ∩ B) := by
  -- `A` and `B` are closed and satisfy `P2`, hence they are open.
  have hOpenA : IsOpen A :=
    Topology.closed_P2_isOpen (X := X) (A := A) hA_closed hP2A
  have hOpenB : IsOpen B :=
    Topology.closed_P2_isOpen (X := X) (A := B) hB_closed hP2B
  -- The intersection of two open sets is open, and open sets satisfy `P2`.
  simpa using
    isOpen_inter_imp_P2 (X := X) (A := A) (B := B) hOpenA hOpenB

theorem P3_closure_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P1 (closure A) := by
  intro hP3
  -- `P3 (closure A)` implies `closure A` is open.
  have hOpen : IsOpen (closure A) :=
    Topology.P3_closure_isOpen_closure (X := X) (A := A) hP3
  -- Openness yields `P1`.
  exact Topology.isOpen_closure_imp_P1 (X := X) (A := A) hOpen

theorem closureInterior_inter_eq_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∩ B)) = closure (A ∩ B) := by
  -- Since `A` and `B` are open, so is their intersection.
  have h_open : IsOpen (A ∩ B) := IsOpen.inter hA hB
  -- The interior of an open set is itself.
  have h_int : interior (A ∩ B) = A ∩ B := by
    simpa using h_open.interior_eq
  -- Rewrite using `h_int`.
  simpa [h_int]

theorem interior_nonempty_imp_nonempty {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : (interior A).Nonempty) : A.Nonempty := by
  rcases h with ⟨x, hx⟩
  exact ⟨x, interior_subset hx⟩

theorem closureInteriorClosure_eq_closure_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (h_open : IsOpen A) :
    closure (interior (closure A)) = closure A := by
  -- From the openness of `A`, we obtain `P1 (closure A)`.
  have hP1 : Topology.P1 (closure A) :=
    Topology.isOpen_imp_P1_closure (X := X) (A := A) h_open
  -- Translate `P1 (closure A)` into the desired equality.
  exact
    (Topology.P1_closure_iff_closureInterior_eq_closure (X := X) (A := A)).1 hP1

theorem closed_P2_imp_closureInterior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) :
    closure (interior A) = A := by
  -- First, use closedness together with `P2` to obtain `P1`.
  have hP1 : Topology.P1 A :=
    closed_P2_imp_P1 (X := X) (A := A) hA_closed hP2
  -- Translate `P1` into the desired equality via the closed‐set characterization.
  exact
    (closed_P1_iff_closure_interior_eq (X := X) (A := A) hA_closed).1 hP1

theorem P2_closure_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (closure A)) :
    Topology.P1 (closure A) := by
  simpa [closure_closure] using
    (Topology.P2_imp_P1_closure (X := X) (A := closure A)) hP2

theorem closed_P2_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  exact
    (Topology.closed_P2_iff_P3 (X := X) (A := A) hA_closed).1 hP2

theorem closed_P3_imp_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    IsOpen A ∧ IsClosed A := by
  have hOpen : IsOpen A :=
    Topology.closed_P3_isOpen (X := X) (A := A) hA_closed hP3
  exact And.intro hOpen hA_closed

theorem P2_subset_closureInterior_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP2 : Topology.P2 A) (hAB : A ⊆ B) :
    A ⊆ closure (interior B) := by
  -- Upgrade `P2 A` to `P1 A`.
  have hP1 : Topology.P1 A :=
    Topology.P2_imp_P1 (X := X) (A := A) hP2
  -- Use the existing lemma for `P1`.
  exact
    Topology.P1_subset_closureInterior_of_subset
      (X := X) (A := A) (B := B) hP1 hAB

theorem Set.mem_interior {α : Type*} [TopologicalSpace α] {s : Set α} {x : α} :
    x ∈ interior s ↔ ∃ U : Set α, IsOpen U ∧ U ⊆ s ∧ x ∈ U := by
  constructor
  · intro hx
    exact ⟨interior s, isOpen_interior, interior_subset, hx⟩
  · rintro ⟨U, hU_open, hU_subset, hxU⟩
    have hU_in_int : U ⊆ interior s := interior_maximal hU_subset hU_open
    exact hU_in_int hxU

theorem interior_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B) ⊆ interior A \ closure B := by
  intro x hx
  -- Choose an open neighbourhood `U` of `x` contained in `A \ B`.
  rcases (Set.mem_interior).1 hx with ⟨U, hU_open, hU_sub, hxU⟩
  -- `U` is contained in `A`.
  have hU_subA : U ⊆ A := by
    intro y hyU
    have h := hU_sub hyU
    exact h.1
  -- Hence `x ∈ interior A`.
  have hx_intA : x ∈ interior A :=
    (Set.mem_interior).2 ⟨U, hU_open, hU_subA, hxU⟩
  -- Show that `x ∉ closure B` using the open set `U` that avoids `B`.
  have hx_notClB : x ∉ closure B := by
    intro hxClB
    -- Any open set containing `x` must meet `B`, contradicting `U ∩ B = ∅`.
    have hNon : (U ∩ B).Nonempty :=
      (mem_closure_iff).1 hxClB U hU_open hxU
    rcases hNon with ⟨y, hyU, hyB⟩
    have hNotB : y ∉ B := by
      have h' := hU_sub hyU
      exact h'.2
    exact hNotB hyB
  -- Assemble the membership in the difference set.
  exact And.intro hx_intA hx_notClB

theorem closureInteriorClosureInteriorClosure_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior (closure (interior (closure A))))) := by
  have h_open : IsOpen (interior (closure (interior (closure A)))) := isOpen_interior
  simpa using
    Topology.isOpen_imp_P1_closure (X := X)
      (A := interior (closure (interior (closure A)))) h_open

theorem P1_subset_closureInterior_of_closure_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP1 : Topology.P1 A) (hcl : closure A ⊆ B) :
    A ⊆ closure (interior B) := by
  -- First derive the simpler inclusion `A ⊆ B`.
  have hAB : A ⊆ B := by
    intro x hxA
    exact hcl (subset_closure hxA)
  -- Apply the existing lemma that works with a direct subset.
  exact
    Topology.P1_subset_closureInterior_of_subset (X := X)
      (A := A) (B := B) hP1 hAB

theorem interior_diff_subset_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B) ⊆ interior A := by
  have h : A \ B ⊆ A := Set.diff_subset
  exact interior_mono h

theorem isOpen_diff_closed_imp_P2 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsClosed B) :
    Topology.P2 (A \ B) := by
  -- `A \ B` is the intersection of two open sets: `A` and `Bᶜ`.
  have hOpenDiff : IsOpen (A \ B) := by
    -- The complement of a closed set is open.
    have hOpenCompl : IsOpen (Bᶜ) := by
      simpa using (isOpen_compl_iff).2 hB
    -- The intersection of two open sets is open.
    simpa [Set.diff_eq] using hA.inter hOpenCompl
  -- Any open set satisfies `P2`.
  simpa using
    Topology.isOpen_imp_P2 (X := X) (A := A \ B) hOpenDiff

theorem isOpen_diff_closed_imp_P3 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsClosed B) :
    Topology.P3 (A \ B) := by
  have hOpenDiff : IsOpen (A \ B) := by
    -- The complement of a closed set is open.
    have hOpenCompl : IsOpen (Bᶜ) := by
      simpa using (isOpen_compl_iff).2 hB
    -- `A \ B` is the intersection of two open sets.
    simpa [Set.diff_eq] using hA.inter hOpenCompl
  -- Any open set satisfies `P3`.
  simpa using
    Topology.isOpen_imp_P3 (X := X) (A := A \ B) hOpenDiff

theorem isOpen_diff_closed_imp_P1 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsClosed B) :
    Topology.P1 (A \ B) := by
  -- `A \ B` can be written as the intersection of the open set `A`
  -- and the open complement of the closed set `B`.
  have hOpenDiff : IsOpen (A \ B) := by
    -- The complement of a closed set is open.
    have hOpenCompl : IsOpen (Bᶜ) := by
      simpa using (isOpen_compl_iff).2 hB
    -- The intersection of two open sets is open.
    simpa [Set.diff_eq] using hA.inter hOpenCompl
  -- Any open set satisfies `P1`.
  simpa using
    Topology.isOpen_imp_P1 (X := X) (A := A \ B) hOpenDiff

theorem P2_subset_closureInteriorClosureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) :
    A ⊆ closure (interior (closure (interior A))) := by
  -- First, upgrade `P2 A` to `P1 A`.
  have hP1 : Topology.P1 A :=
    Topology.P2_imp_P1 (X := X) (A := A) hP2
  -- Then apply the established result for `P1 A`.
  exact
    P1_subset_closureInteriorClosureInterior (X := X) (A := A) hP1

theorem interior_subset_interiorClosureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ interior (closure (interior (closure A))) := by
  intro x hx
  -- Step 1: upgrade `hx` to membership in `interior (closure A)`.
  have hx₁ : x ∈ interior (closure A) := by
    have h₁ : interior A ⊆ interior (closure A) :=
      interior_subset_interiorClosure (X := X) (A := A)
    exact h₁ hx
  -- Step 2: show `interior (closure A)` is contained in the larger interior.
  have h₂ :
      interior (closure A) ⊆ interior (closure (interior (closure A))) := by
    have h_cl : interior (closure A) ⊆ closure (interior (closure A)) :=
      subset_closure
    have h_open : IsOpen (interior (closure A)) := isOpen_interior
    exact interior_maximal h_cl h_open
  exact h₂ hx₁

theorem P2_subset_closureInterior_of_closure_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP2 : Topology.P2 A) (hcl : closure A ⊆ B) :
    A ⊆ closure (interior B) := by
  -- First, upgrade `P2 A` to `P1 A`.
  have hP1 : Topology.P1 A :=
    Topology.P2_imp_P1 (X := X) (A := A) hP2
  -- Then apply the existing lemma for `P1`.
  exact
    Topology.P1_subset_closureInterior_of_closure_subset
      (X := X) (A := A) (B := B) hP1 hcl

theorem interior_diff_closed_eq {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB_closed : IsClosed B) :
    interior (A \ B) = interior A \ B := by
  classical
  -- Prove the mutual inclusions.
  apply Set.Subset.antisymm
  · -- `interior (A \ B) ⊆ interior A \ B`
    intro x hx
    -- We already have the more precise inclusion into `interior A \ closure B`.
    have hsubset : interior (A \ B) ⊆ interior A \ closure B :=
      interior_diff_subset (X := X) (A := A) (B := B)
    have hx' := hsubset hx
    -- Since `B` is closed, `closure B = B`.
    simpa [hB_closed.closure_eq] using hx'
  · -- `interior A \ B ⊆ interior (A \ B)`
    rintro x ⟨hxIntA, hxNotB⟩
    -- Choose an open neighbourhood `U` of `x` contained in `A`.
    rcases (Set.mem_interior).1 hxIntA with ⟨U, hU_open, hU_subA, hxU⟩
    -- Consider the open set `V = U \ B`.
    have hV_open : IsOpen (U \ B) := by
      -- The complement of `B` is open because `B` is closed.
      have hOpenCompl : IsOpen (Bᶜ) := by
        simpa using (isOpen_compl_iff).2 hB_closed
      -- `U \ B = U ∩ Bᶜ`.
      simpa [Set.diff_eq] using hU_open.inter hOpenCompl
    -- `V` is contained in `A \ B`.
    have hV_sub : U \ B ⊆ A \ B := by
      intro y hy
      rcases hy with ⟨hyU, hyNotB⟩
      exact And.intro (hU_subA hyU) hyNotB
    -- `x` lies in `V`.
    have hxV : x ∈ U \ B := by
      exact And.intro hxU hxNotB
    -- Conclude that `x` is in the interior of `A \ B`.
    exact
      (Set.mem_interior).2 ⟨U \ B, hV_open, hV_sub, hxV⟩

theorem interior_diff_subset_closure_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A \ B) ⊆ closure A := by
  intro x hx
  -- From `x ∈ interior (A \ B)` we obtain `x ∈ A \ B`.
  have h_mem : x ∈ A \ B := interior_subset hx
  -- Hence `x ∈ A`.
  have hxA : x ∈ A := h_mem.1
  -- Since `A ⊆ closure A`, we conclude `x ∈ closure A`.
  exact subset_closure hxA

theorem closure_diff_subset_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A \ B) ⊆ closure A := by
  have h : A \ B ⊆ A := Set.diff_subset
  exact closure_mono h

theorem isClosed_imp_P1_compl {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P1 (Aᶜ) := by
  have hOpen : IsOpen (Aᶜ) := (isOpen_compl_iff).2 hA_closed
  simpa using Topology.isOpen_imp_P1 (X := X) (A := Aᶜ) hOpen

theorem interior_closure_iUnion_subset_interior_closure_iUnion
    {X ι : Type*} [TopologicalSpace X] (A : ι → Set X) :
    (⋃ i, interior (closure (A i))) ⊆
      interior (closure (⋃ i, A i)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have h_closure : closure (A i) ⊆ closure (⋃ j, A j) := by
    have h_subset : A i ⊆ ⋃ j, A j := by
      intro y hy; exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact closure_mono h_subset
  have h_interior :
      interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) :=
    interior_mono h_closure
  exact h_interior hx_i

theorem isClosed_imp_P2_compl {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 (Aᶜ) := by
  have hA_open : IsOpen (Aᶜ) := (isOpen_compl_iff).2 hA_closed
  simpa using Topology.isOpen_imp_P2 (X := X) (A := Aᶜ) hA_open

theorem interior_diff_subset_closure_diff {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A \ B) ⊆ closure A \ B := by
  intro x hx
  -- From `hx : x ∈ interior (A \ B)` we deduce `x ∈ A \ B`.
  have h_mem : x ∈ A \ B := interior_subset hx
  -- Using the existing lemma, we know `x ∈ closure A`.
  have h_cl : x ∈ closure A :=
    interior_diff_subset_closure_left (X := X) (A := A) (B := B) hx
  -- Assemble the membership in the required difference set.
  exact And.intro h_cl h_mem.2

theorem isClosed_imp_P3_compl {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P3 (Aᶜ) := by
  have hA_open : IsOpen (Aᶜ) := (isOpen_compl_iff).2 hA_closed
  simpa using Topology.isOpen_imp_P3 (X := X) (A := Aᶜ) hA_open

theorem P1_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A) (hB : Topology.P1 B) :
    Topology.P1 (closure A ∪ closure B) := by
  -- First, lift `P1` from `A` and `B` to their closures.
  have hA_cl : Topology.P1 (closure A) :=
    Topology.P1_imp_P1_closure (X := X) (A := A) hA
  have hB_cl : Topology.P1 (closure B) :=
    Topology.P1_imp_P1_closure (X := X) (A := B) hB
  -- Apply the existing union lemma for `P1`.
  exact
    Topology.P1_union (X := X) (A := closure A) (B := closure B) hA_cl hB_cl

theorem closureInterior_nonempty_iff_interior_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (interior A)).Nonempty ↔ (interior A).Nonempty := by
  classical
  constructor
  · intro hCl
    by_contra hIntEmpty
    have hIntEq : interior A = (∅ : Set X) :=
      Set.not_nonempty_iff_eq_empty.mp hIntEmpty
    have hClEq : closure (interior A) = (∅ : Set X) := by
      simpa [hIntEq, closure_empty] using rfl
    rcases hCl with ⟨x, hx⟩
    have : (x : X) ∈ (∅ : Set X) := by
      simpa [hClEq] using hx
    exact this.elim
  · intro hInt
    exact hInt.mono (subset_closure : interior A ⊆ closure (interior A))

theorem closure_inter_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B) ⊆ closure A ∩ closure B := by
  intro x hx
  have hA : x ∈ closure A := (closure_mono (Set.inter_subset_left)) hx
  have hB : x ∈ closure B := (closure_mono (Set.inter_subset_right)) hx
  exact And.intro hA hB

theorem P2_subset_interiorClosure_of_closure_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP2 : Topology.P2 A) (hcl : closure A ⊆ B) :
    A ⊆ interior (closure B) := by
  -- First, derive `A ⊆ B` from the hypothesis `closure A ⊆ B`.
  have hAB : A ⊆ B := fun x hxA => hcl (subset_closure hxA)
  -- Upgrade `P2 A` to `P3 A`.
  have hP3 : Topology.P3 A :=
    Topology.P2_imp_P3 (X := X) (A := A) hP2
  -- Apply the existing lemma for `P3` with the inclusion `A ⊆ B`.
  exact
    P3_subset_interiorClosure_of_subset (X := X) (A := A) (B := B) hP3 hAB

theorem interior_closure_P1_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure A)) ↔ Topology.P3 (interior (closure A)) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  simpa using
    Topology.isOpen_P1_iff_P3 (X := X) (A := interior (closure A)) h_open

theorem closureInterior_union_P1 {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (closure (interior A) ∪ closure (interior B)) := by
  -- Each `closure (interior _)` individually satisfies `P1`.
  have hA : Topology.P1 (closure (interior A)) :=
    closureInterior_P1 (X := X) (A := A)
  have hB : Topology.P1 (closure (interior B)) :=
    closureInterior_P1 (X := X) (A := B)
  -- The union of two `P1` sets is again `P1`.
  exact
    Topology.P1_union (X := X)
      (A := closure (interior A)) (B := closure (interior B)) hA hB

theorem interior_diff_eq_self_diff_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) :
    interior (A \ B) = A \ closure B := by
  classical
  -- First inclusion: `interior (A \ B) ⊆ A \ closure B`.
  have h₁ : interior (A \ B) ⊆ A \ closure B := by
    -- We already have a more precise inclusion into `interior A \ closure B`;
    -- for an open set `A`, `interior A = A`.
    have h := interior_diff_subset (X := X) (A := A) (B := B)
    simpa [hA.interior_eq] using h
  -- Second inclusion: `A \ closure B ⊆ interior (A \ B)`.
  have h₂ : A \ closure B ⊆ interior (A \ B) := by
    -- The set `A \ closure B` is open.
    have hOpenDiff : IsOpen (A \ closure B) := by
      -- `closure B` is closed, hence its complement is open.
      have hOpenCompl : IsOpen ((closure B)ᶜ) := by
        have hClosed : IsClosed (closure B) := isClosed_closure
        simpa using (isOpen_compl_iff).2 hClosed
      -- `A \ closure B` is the intersection of two open sets.
      simpa [Set.diff_eq] using hA.inter hOpenCompl
    -- Moreover, `A \ closure B ⊆ A \ B` because `B ⊆ closure B`.
    have hSubset : A \ closure B ⊆ A \ B := by
      intro x hx
      rcases hx with ⟨hxA, hxNotCl⟩
      have hxNotB : x ∉ B := by
        intro hxB
        have : (x : X) ∈ closure B := subset_closure hxB
        exact hxNotCl this
      exact And.intro hxA hxNotB
    -- Use the maximality property of the interior.
    exact interior_maximal hSubset hOpenDiff
  -- Combine the two inclusions for equality.
  exact Set.Subset.antisymm h₁ h₂

theorem interior_closure_eq_closure_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure A)) :
    interior (closure A) = closure A := by
  simpa using h_open.interior_eq

theorem interior_closure_interior_eq_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    interior (closure (interior A)) = interior A := by
  apply Set.Subset.antisymm
  ·
    have h_subset : closure (interior A) ⊆ A :=
      closure_interior_subset_of_isClosed (X := X) (A := A) hA_closed
    exact interior_mono h_subset
  ·
    exact interior_subset_interiorClosureInterior (X := X) (A := A)

theorem interior_eq_self_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_int : interior A = A) :
    Topology.P3 A := by
  have hOpen : IsOpen A := by
    simpa [h_int] using (isOpen_interior : IsOpen (interior A))
  simpa using Topology.isOpen_imp_P3 (X := X) (A := A) hOpen

theorem closureInterior_diff_subset_closureInterior_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B)) ⊆ closure (interior A) := by
  -- The interior of a set difference is contained in the interior of the left set.
  have h : interior (A \ B) ⊆ interior A :=
    interior_diff_subset_left (X := X) (A := A) (B := B)
  -- Taking closures preserves inclusions.
  exact closure_mono h

theorem isOpen_diff_closed_imp_P1_P2_P3 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) (hB : IsClosed B) :
    Topology.P1 (A \ B) ∧ Topology.P2 (A \ B) ∧ Topology.P3 (A \ B) := by
  have hP1 : Topology.P1 (A \ B) :=
    isOpen_diff_closed_imp_P1 (X := X) (A := A) (B := B) hA hB
  have hP2 : Topology.P2 (A \ B) :=
    isOpen_diff_closed_imp_P2 (X := X) (A := A) (B := B) hA hB
  have hP3 : Topology.P3 (A \ B) :=
    isOpen_diff_closed_imp_P3 (X := X) (A := A) (B := B) hA hB
  exact And.intro hP1 (And.intro hP2 hP3)

theorem P3_closure_imp_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P2 (closure A) := by
  intro hP3
  exact (Topology.P3_closure_iff_P2_closure (X := X) (A := A)).1 hP3

theorem closure_diff_subset_closure_left_diff_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A \ B) ⊆ closure A \ interior B := by
  intro x hx
  -- `x ∈ closure A` follows from monotonicity of the closure operator.
  have hxClA : x ∈ closure A := by
    have h_subset : A \ B ⊆ A := Set.diff_subset
    exact (closure_mono h_subset) hx
  -- Show that `x ∉ interior B`.
  have hxNotIntB : x ∉ interior B := by
    intro hxIntB
    -- Use the neighbourhood `interior B`, which is open and contains `x`.
    have h_non : (interior B ∩ (A \ B)).Nonempty := by
      have h_closure :=
        (mem_closure_iff).1 hx (interior B) isOpen_interior hxIntB
      simpa using h_closure
    rcases h_non with ⟨y, hyIntB, hyDiff⟩
    -- `y ∈ interior B` implies `y ∈ B`, contradicting `y ∈ A \ B`.
    have hyB : y ∈ B := interior_subset hyIntB
    exact hyDiff.2 hyB
  exact And.intro hxClA hxNotIntB

theorem interior_diff_subset_interior_diff {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB_closed : IsClosed B) :
    interior A \ closure B ⊆ interior (A \ B) := by
  intro x hx
  rcases hx with ⟨hxIntA, hxNotClB⟩
  -- Choose an open neighbourhood `U` of `x` contained in `A`.
  rcases (Set.mem_interior).1 hxIntA with ⟨U, hU_open, hU_subA, hxU⟩
  -- The complement of the closed set `B` is open.
  have hOpenCompl : IsOpen (Bᶜ) := by
    simpa using (isOpen_compl_iff).2 hB_closed
  -- `x` is not in `B`.
  have hxNotB : x ∉ B := by
    intro hxB
    have : (x : X) ∈ closure B := subset_closure hxB
    exact hxNotClB this
  -- Define the open set `V = U ∩ Bᶜ`.
  let V : Set X := U ∩ Bᶜ
  have hV_open : IsOpen V := hU_open.inter hOpenCompl
  have hV_sub : V ⊆ A \ B := by
    intro y hyV
    have hyA : y ∈ A := hU_subA hyV.1
    have hyNotB : y ∉ B := hyV.2
    exact And.intro hyA hyNotB
  have hxV : x ∈ V := And.intro hxU hxNotB
  -- Conclude that `x ∈ interior (A \ B)`.
  exact
    (Set.mem_interior).2 ⟨V, hV_open, hV_sub, hxV⟩

theorem isOpen_closure_iff_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsOpen (closure A) ↔ interior (closure A) = closure A := by
  constructor
  · intro h_open
    simpa using h_open.interior_eq
  · intro h_eq
    have h_open_int : IsOpen (interior (closure A)) := isOpen_interior
    simpa [h_eq] using h_open_int

theorem interior_union_subset_interiorUnion {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `interior A` is monotone with respect to inclusion.
      have h_subset : A ⊆ A ∪ B := by
        intro y hy; exact Or.inl hy
      have h_incl : interior A ⊆ interior (A ∪ B) := interior_mono h_subset
      exact h_incl hxA
  | inr hxB =>
      -- Symmetric argument for `interior B`.
      have h_subset : B ⊆ A ∪ B := by
        intro y hy; exact Or.inr hy
      have h_incl : interior B ⊆ interior (A ∪ B) := interior_mono h_subset
      exact h_incl hxB

theorem interior_closure_interior_closure_interior_closure_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure (interior (closure (interior (closure A)))))) := by
  have h_open :
      IsOpen (interior (closure (interior (closure (interior (closure A)))))) :=
    isOpen_interior
  simpa using
    Topology.isOpen_imp_P1
      (X := X)
      (A := interior (closure (interior (closure (interior (closure A)))))) h_open

theorem P2_subset_closureInterior_of_subset' {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP2 : Topology.P2 A) (hAB : A ⊆ B) :
    A ⊆ closure (interior B) := by
  dsimp [Topology.P2] at hP2
  intro x hxA
  -- Step 1: use `P2` to move from `A` into `interior (closure (interior A))`.
  have hx₁ : x ∈ interior (closure (interior A)) := hP2 hxA
  -- Step 2: relate that interior to `closure (interior B)`.
  have h_incl : interior (closure (interior A)) ⊆ closure (interior B) := by
    -- `interior A ⊆ interior B` by monotonicity.
    have h_int : interior A ⊆ interior B := interior_mono hAB
    -- Taking closures preserves inclusions.
    have h_clos : closure (interior A) ⊆ closure (interior B) :=
      closure_mono h_int
    -- Interiority is monotone as well.
    have h_int_clos :
        interior (closure (interior A)) ⊆
          interior (closure (interior B)) :=
      interior_mono h_clos
    -- Finally, `interior (closure (interior B)) ⊆ closure (interior B)`.
    exact Set.Subset.trans h_int_clos interior_subset
  exact h_incl hx₁

theorem interior_inter_subset_inter_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B) ⊆ interior A ∩ interior B := by
  intro x hx
  have hA : x ∈ interior A := by
    have h_sub : A ∩ B ⊆ A := Set.inter_subset_left
    exact (interior_mono h_sub) hx
  have hB : x ∈ interior B := by
    have h_sub : A ∩ B ⊆ B := Set.inter_subset_right
    exact (interior_mono h_sub) hx
  exact And.intro hA hB

theorem P1_subset_of_closureInterior_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP1 : Topology.P1 A) (hsubset : closure (interior A) ⊆ B) :
    A ⊆ B := by
  dsimp [Topology.P1] at hP1
  intro x hxA
  exact hsubset (hP1 hxA)

theorem denseInterior_imp_closureInteriorClosure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    closure (interior (closure A)) = closure A := by
  -- From the density assumption we get `closure A = univ`.
  have h_closure_univ : closure A = (Set.univ : Set X) :=
    closure_eq_univ_of_denseInterior (X := X) (A := A) h_dense
  -- And we also have `interior (closure A) = univ`.
  have h_int_univ : interior (closure A) = (Set.univ : Set X) :=
    interior_closure_eq_univ_of_denseInterior (X := X) (A := A) h_dense
  -- Rewrite both sides using these identities.
  calc
    closure (interior (closure A))
        = closure (Set.univ : Set X) := by
          simpa [h_int_univ]
    _ = (Set.univ : Set X) := by
          simpa [closure_univ]
    _ = closure A := by
          simpa [h_closure_univ]

theorem isOpen_imp_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure A)) :
    Topology.P2 (closure A) := by
  simpa using
    Topology.isOpen_imp_P2 (X := X) (A := closure A) h_open

theorem P1_imp_closure_subset_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    closure A ⊆ closure (interior (closure A)) := by
  -- First, translate `P1 A` into an inclusion between closures.
  have h₁ : closure A ⊆ closure (interior A) :=
    (Topology.P1_iff_closure_subset_closureInterior (X := X) (A := A)).1 hP1
  -- Next, widen the target from `closure (interior A)` to
  -- `closure (interior (closure A))` using monotonicity.
  have h₂ : closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_interior_subset_closure_interior_closure (X := X) (A := A)
  -- Combine the two inclusions.
  exact Set.Subset.trans h₁ h₂

theorem interior_closure_interior_eq_univ_iff_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) = (Set.univ : Set X) ↔
      closure (interior A) = (Set.univ : Set X) := by
  constructor
  · intro hInt
    -- Since `interior (closure (interior A)) ⊆ closure (interior A)`,
    -- we obtain the reverse inclusion from the hypothesis.
    have h_subset : (Set.univ : Set X) ⊆ closure (interior A) := by
      simpa [hInt] using
        (interior_subset :
          interior (closure (interior A)) ⊆ closure (interior A))
    exact Set.Subset.antisymm (Set.subset_univ _) h_subset
  · intro hCl
    -- Rewrite the left‐hand side using `hCl` and compute the interior of `univ`.
    have : interior (closure (interior A)) =
        interior (Set.univ : Set X) := by
      simpa [hCl]
    simpa [interior_univ] using this

theorem closed_P1_compl_iff_P2_compl {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P1 (Aᶜ) ↔ Topology.P2 (Aᶜ) := by
  -- The complement of a closed set is open.
  have hA_open : IsOpen (Aᶜ) := (isOpen_compl_iff).2 hA_closed
  -- Apply the existing equivalence for open sets.
  simpa using Topology.isOpen_P1_iff_P2 (X := X) (A := Aᶜ) hA_open

theorem interior_subset_closureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure (interior A) := by
  intro x hx
  exact subset_closure hx

theorem interior_inter_interior_subset_interior_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∩ interior B ⊆ interior (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hA, hB⟩
  -- The set `U = interior A ∩ interior B` is an open neighbourhood of `x`
  -- contained in `A ∩ B`.
  have hU_open : IsOpen (interior A ∩ interior B) :=
    isOpen_interior.inter isOpen_interior
  have hU_subset : interior A ∩ interior B ⊆ A ∩ B := by
    intro y hy
    exact ⟨interior_subset hy.1, interior_subset hy.2⟩
  -- Hence `x` belongs to the interior of `A ∩ B`.
  exact
    (Set.mem_interior).2 ⟨interior A ∩ interior B, hU_open, hU_subset, ⟨hA, hB⟩⟩

theorem P1_of_subset_and_subset_closureInterior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP1A : Topology.P1 A) (hAB : A ⊆ B) (hBsubset : B ⊆ closure (interior A)) :
    Topology.P1 B := by
  dsimp [Topology.P1] at hP1A ⊢
  intro x hxB
  -- Step 1: Use the hypothesis `hBsubset` to place `x` in `closure (interior A)`.
  have hxClA : x ∈ closure (interior A) := hBsubset hxB
  -- Step 2: Relate `closure (interior A)` to `closure (interior B)`
  -- via the monotonicity of `interior` and `closure`.
  have hClSub : closure (interior A) ⊆ closure (interior B) := by
    have hIntSub : interior A ⊆ interior B := interior_mono hAB
    exact closure_mono hIntSub
  -- Step 3: Conclude the desired membership.
  exact hClSub hxClA

theorem interior_closure_diff_subset_interior_closure_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A \ B)) ⊆ interior (closure A) := by
  -- `A \ B` is contained in `A`.
  have h_subset : A \ B ⊆ A := Set.diff_subset
  -- Taking closures preserves inclusions.
  have h_closure_subset : closure (A \ B) ⊆ closure A :=
    closure_mono h_subset
  -- Applying `interior` (a monotone operator) to both sides
  -- yields the desired inclusion.
  exact interior_mono h_closure_subset

theorem interior_subset_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure (interior (closure A)) := by
  intro x hx
  -- First, move from `interior A` to `interior (closure A)`.
  have hx₁ : x ∈ interior (closure A) :=
    (interior_subset_interiorClosure (X := X) (A := A)) hx
  -- Then, use the fact that any set is contained in the closure of itself.
  have hx₂ : x ∈ closure (interior (closure A)) :=
    (subset_closure : interior (closure A) ⊆
      closure (interior (closure A))) hx₁
  exact hx₂

theorem closed_P1_compl_iff_P3_compl {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P1 (Aᶜ) ↔ Topology.P3 (Aᶜ) := by
  have h_open : IsOpen (Aᶜ) := (isOpen_compl_iff).2 hA_closed
  simpa using
    Topology.isOpen_P1_iff_P3 (X := X) (A := Aᶜ) h_open

theorem nonempty_of_closureInterior_nonempty {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (interior A)).Nonempty → A.Nonempty := by
  intro hClInt
  -- First, turn non-emptiness of `closure (interior A)` into non-emptiness of `interior A`.
  have hInt : (interior A).Nonempty :=
    ((closureInterior_nonempty_iff_interior_nonempty (X := X) (A := A)).1 hClInt)
  -- Then use the fact that a non-empty interior forces the original set to be non-empty.
  exact interior_nonempty_imp_nonempty (X := X) (A := A) hInt

theorem closed_P2_compl_iff_P3_compl {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 (Aᶜ) ↔ Topology.P3 (Aᶜ) := by
  -- The complement of a closed set is open.
  have hA_open : IsOpen (Aᶜ) := (isOpen_compl_iff).2 hA_closed
  -- Use the existing equivalence for open sets.
  simpa using
    Topology.isOpen_P2_iff_P3 (X := X) (A := Aᶜ) hA_open

theorem P2_interior_interior_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (interior A)) ↔ Topology.P2 (interior A) := by
  simpa [interior_interior]

theorem interior_closure_inter_interior_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ interior B)) ⊆ interior (closure B) := by
  -- First note that `A ∩ interior B ⊆ B`.
  have h_sub : A ∩ interior B ⊆ B := by
    intro x hx
    exact (interior_subset : interior B ⊆ B) hx.2
  -- Taking closures preserves inclusions.
  have h_closure : closure (A ∩ interior B) ⊆ closure B := closure_mono h_sub
  -- Applying `interior_mono` yields the desired inclusion.
  exact interior_mono h_closure

theorem isOpen_P1_inter_imp_P1 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hP1B : Topology.P1 B) :
    Topology.P1 (A ∩ B) := by
  dsimp [Topology.P1] at hP1B ⊢
  intro x hx
  -- Decompose the membership `x ∈ A ∩ B`.
  have hxA : x ∈ A := hx.1
  have hxB : x ∈ B := hx.2
  -- Apply `P1 B` to obtain `x ∈ closure (interior B)`.
  have hxClB : x ∈ closure (interior B) := hP1B hxB
  -- We first show that `x ∈ closure (A ∩ interior B)`.
  have hxClAIntB : x ∈ closure (A ∩ interior B) := by
    -- Use the neighborhood characterization of the closure.
    apply (mem_closure_iff).2
    intro U hUopen hxU
    -- Consider the open neighborhood `U ∩ A` of `x`.
    have hUA_open : IsOpen (U ∩ A) := hUopen.inter hA
    have hxUA : x ∈ U ∩ A := And.intro hxU hxA
    -- Since `x ∈ closure (interior B)`, this neighborhood meets `interior B`.
    have hNon : (U ∩ A ∩ interior B).Nonempty :=
      (mem_closure_iff).1 hxClB (U ∩ A) hUA_open hxUA
    -- Rewriting yields the required non‐emptiness.
    simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hNon
  -- Show that `A ∩ interior B` is contained in `interior (A ∩ B)`.
  have hSubset : A ∩ interior B ⊆ interior (A ∩ B) := by
    intro y hy
    -- The set `A ∩ interior B` is open.
    have hOpen : IsOpen (A ∩ interior B) := hA.inter isOpen_interior
    -- It is contained in `A ∩ B`.
    have hSub : A ∩ interior B ⊆ A ∩ B := by
      intro z hz
      exact And.intro hz.1 (interior_subset hz.2)
    -- Hence each of its points lies in the interior of `A ∩ B`.
    exact
      (Set.mem_interior).2 ⟨A ∩ interior B, hOpen, hSub, hy⟩
  -- Monotonicity of the closure yields the desired membership.
  exact (closure_mono hSubset) hxClAIntB

theorem P3_of_subset_and_subset_interiorClosure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hBsubset : B ⊆ interior (closure A)) :
    Topology.P3 B := by
  dsimp [Topology.P3] at *
  intro x hxB
  -- From `hxB : x ∈ B` and `hBsubset`, we obtain `x ∈ interior (closure A)`.
  have hxIntClA : x ∈ interior (closure A) := hBsubset hxB
  -- Since `A ⊆ B`, we have `closure A ⊆ closure B`.
  have hClSub : closure A ⊆ closure B := closure_mono hAB
  -- Taking interiors preserves inclusions.
  have hIntSub : interior (closure A) ⊆ interior (closure B) :=
    interior_mono hClSub
  -- Combine the two facts to place `x` in `interior (closure B)`.
  exact hIntSub hxIntClA

theorem interior_inter_eq_left_inter_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsOpen A) :
    interior (A ∩ B) = A ∩ interior B := by
  apply Set.Subset.antisymm
  ·
    have h :=
      interior_inter_subset_inter_interior (X := X) (A := A) (B := B)
    simpa [hA.interior_eq] using h
  ·
    have hOpen : IsOpen (A ∩ interior B) := hA.inter isOpen_interior
    have hSub : A ∩ interior B ⊆ A ∩ B := by
      intro x hx
      exact And.intro hx.1 (interior_subset hx.2)
    exact (interior_maximal hSub hOpen)

theorem isOpen_inter_imp_P3 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P3 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B) := IsOpen.inter hA hB
  simpa using
    Topology.isOpen_imp_P3 (X := X) (A := A ∩ B) hOpen

theorem closure_inter_interior_subset_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hB : IsClosed B) :
    closure (A ∩ interior B) ⊆ B := by
  -- `interior B` is contained in `B`.
  have h_subset : A ∩ interior B ⊆ B := by
    intro x hx
    exact (interior_subset : interior B ⊆ B) hx.2
  -- Taking closures preserves inclusions.
  have h_closure : closure (A ∩ interior B) ⊆ closure B :=
    closure_mono h_subset
  -- Since `B` is closed, `closure B = B`.
  simpa [hB.closure_eq] using h_closure

theorem interior_subset_closureInteriorClosureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure (interior (closure (interior A))) := by
  intro x hx
  -- `interior A ⊆ closure (interior A)`
  have hxCl : (x : X) ∈ closure (interior A) := subset_closure hx
  -- `closure (interior A) ⊆ closure (interior (closure (interior A)))`
  have hIncl :
      closure (interior A) ⊆ closure (interior (closure (interior A))) := by
    have h :=
      closure_interior_subset_closure_interior_closure
        (X := X) (A := interior A)
    simpa [interior_interior] using h
  exact hIncl hxCl

theorem closure_interior_subset_closure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    closure (interior A) ⊆ closure B := by
  -- `interior A` is contained in `A`, hence in `B`.
  have h : interior A ⊆ B := fun x hx => hAB (interior_subset hx)
  -- Taking closures preserves inclusions.
  exact closure_mono h

theorem isOpen_inter_imp_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P1 (A ∩ B) ∧ Topology.P2 (A ∩ B) ∧ Topology.P3 (A ∩ B) := by
  have hP1 : Topology.P1 (A ∩ B) :=
    isOpen_inter_imp_P1 (X := X) (A := A) (B := B) hA hB
  have hP2 : Topology.P2 (A ∩ B) :=
    isOpen_inter_imp_P2 (X := X) (A := A) (B := B) hA hB
  have hP3 : Topology.P3 (A ∩ B) :=
    isOpen_inter_imp_P3 (X := X) (A := A) (B := B) hA hB
  exact And.intro hP1 (And.intro hP2 hP3)

theorem subset_interiorClosure_of_subset
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hAB : A ⊆ interior (closure B)) (hBC : B ⊆ C) :
    A ⊆ interior (closure C) := by
  intro x hxA
  have hxIntB : x ∈ interior (closure B) := hAB hxA
  have hClos : closure B ⊆ closure C := closure_mono hBC
  have hInt : interior (closure B) ⊆ interior (closure C) := interior_mono hClos
  exact hInt hxIntB

theorem closure_interior_empty_iff_interior_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (∅ : Set X) ↔ interior A = (∅ : Set X) := by
  constructor
  · intro hCl
    -- `interior A` is contained in its closure, which is `∅`.
    have hSub : interior A ⊆ (∅ : Set X) := by
      simpa [hCl] using
        (subset_closure : interior A ⊆ closure (interior A))
    exact Set.Subset.antisymm hSub (Set.empty_subset _)
  · intro hInt
    simpa [hInt, closure_empty]

theorem P3_closure_closure_iff_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (closure A)) ↔ Topology.P2 (closure A) := by
  have h₁ :=
    (P3_closure_closure_iff (X := X) (A := A))   -- P3 (closure (closure A)) ↔ P3 (closure A)
  have h₂ :=
    (P3_closure_iff_P2_closure (X := X) (A := A)) -- P3 (closure A) ↔ P2 (closure A)
  exact h₁.trans h₂

theorem interior_inter_eq_inter_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A ∩ B) = interior A ∩ interior B := by
  apply Set.Subset.antisymm
  ·
    exact
      interior_inter_subset_inter_interior (X := X) (A := A) (B := B)
  ·
    exact
      interior_inter_interior_subset_interior_inter (X := X) (A := A) (B := B)

theorem interior_closure_empty {X : Type*} [TopologicalSpace X] :
    interior (closure (∅ : Set X)) = (∅ : Set X) := by
  simpa [closure_empty, interior_empty]

theorem interior_closure_union_eq_interior_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∪ B)) = interior (closure A ∪ closure B) := by
  simpa [closure_union]

theorem closure_interior_univ {X : Type*} [TopologicalSpace X] :
    closure (interior (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [interior_univ, closure_univ]

theorem closed_P3_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P3 A ↔ interior A = A := by
  constructor
  · intro hP3
    exact closed_P3_interior_eq (X := X) (A := A) hA_closed hP3
  · intro hInt
    have hA_open : IsOpen A := by
      simpa [hInt] using (isOpen_interior : IsOpen (interior A))
    exact Topology.isOpen_imp_P3 (X := X) (A := A) hA_open

theorem closure_interior_inter_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∩ B) ⊆ closure A ∩ closure B := by
  intro x hx
  -- `interior A ∩ B` is contained in `A`.
  have hA : interior A ∩ B ⊆ A := by
    intro y hy
    exact interior_subset hy.1
  -- `interior A ∩ B` is also contained in `B`.
  have hB : interior A ∩ B ⊆ B := by
    intro y hy
    exact hy.2
  -- Monotonicity of `closure` yields the desired memberships.
  have hxA : x ∈ closure A := (closure_mono hA) hx
  have hxB : x ∈ closure B := (closure_mono hB) hx
  exact And.intro hxA hxB



theorem closure_interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior (closure A)))))) =
      closure (interior (closure A)) := by
  -- First, collapse the two outermost layers using an existing lemma.
  have h :
      closure (interior (closure (interior (closure (interior (closure A)))))) =
        closure (interior (closure (closure A))) := by
    simpa using
      (closure_interior_closure_interior_closure_eq (X := X) (A := closure A))
  -- Finally, simplify the remaining `closure` and `interior` of a closure.
  simpa [closure_closure, interior_closure_closure_eq] using h

theorem interior_univ_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_int : interior A = (Set.univ : Set X)) :
    Topology.P1 A := by
  -- From `interior A = univ`, we get `closure (interior A) = univ`.
  have h_dense : closure (interior A) = (Set.univ : Set X) := by
    simpa [h_int, closure_univ]
  -- Apply the existing lemma for dense interior.
  exact Topology.denseInterior_imp_P1 (X := X) (A := A) h_dense

theorem interior_closure_closure_interior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (closure (interior A))) = interior (closure (interior A)) := by
  simpa [closure_closure]

theorem P3_interiorClosure_inter_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 A) :
    interior (closure A) ∩ A = A := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.2
  · intro x hxA
    have hxInt : x ∈ interior (closure A) := hP3 hxA
    exact And.intro hxInt hxA

theorem isClosed_imp_P1_P2_P3_compl {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P1 (Aᶜ) ∧ Topology.P2 (Aᶜ) ∧ Topology.P3 (Aᶜ) := by
  have hP1 : Topology.P1 (Aᶜ) :=
    isClosed_imp_P1_compl (X := X) (A := A) hA_closed
  have hP2 : Topology.P2 (Aᶜ) :=
    isClosed_imp_P2_compl (X := X) (A := A) hA_closed
  have hP3 : Topology.P3 (Aᶜ) :=
    isClosed_imp_P3_compl (X := X) (A := A) hA_closed
  exact And.intro hP1 (And.intro hP2 hP3)

theorem interior_closure_subset_interior_of_closure_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} (h : closure A ⊆ B) :
    interior (closure A) ⊆ interior B := by
  exact interior_mono h

theorem P3_closure_imp_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 (closure A)) :
    interior (closure A) = closure A := by
  -- `P3 (closure A)` implies that `closure A` is open.
  have hOpen : IsOpen (closure A) :=
    Topology.P3_closure_isOpen_closure (X := X) (A := A) hP3
  -- For an open set, its interior is itself.
  simpa using hOpen.interior_eq

theorem interior_inter_eq_inter_interior_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hB : IsOpen B) :
    interior (A ∩ B) = interior A ∩ B := by
  apply Set.Subset.antisymm
  · -- `interior (A ∩ B) ⊆ interior A ∩ B`
    intro x hx
    have h₁ :
        x ∈ interior A ∧ x ∈ interior B :=
      (interior_inter_subset_inter_interior
        (X := X) (A := A) (B := B)) hx
    rcases h₁ with ⟨hIntA, hIntB⟩
    -- Since `B` is open, `interior B = B`.
    have hB_mem : x ∈ B := by
      simpa [hB.interior_eq] using hIntB
    exact And.intro hIntA hB_mem
  · -- `interior A ∩ B ⊆ interior (A ∩ B)`
    intro x hx
    rcases hx with ⟨hxIntA, hxB⟩
    -- The set `V = interior A ∩ B` is an open neighbourhood of `x`
    -- contained in `A ∩ B`.
    have hV_open : IsOpen (interior A ∩ B) :=
      isOpen_interior.inter hB
    have hV_subset : interior A ∩ B ⊆ A ∩ B := by
      intro y hy
      exact And.intro (interior_subset hy.1) hy.2
    have hxV : x ∈ interior A ∩ B := And.intro hxIntA hxB
    exact
      (Set.mem_interior).2 ⟨interior A ∩ B, hV_open, hV_subset, hxV⟩

theorem closureInterior_eq_closure_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure A)) :
    closure (interior (closure A)) = closure A := by
  -- Since `closure A` is open, its interior is itself.
  have h_int : interior (closure A) = closure A := h_open.interior_eq
  -- Taking closures and simplifying yields the desired equality.
  calc
    closure (interior (closure A))
        = closure (closure A) := by
            simpa [h_int]
    _ = closure A := by
            simpa [closure_closure]

theorem closure_inter_subset_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure A ∩ closure B ⊆ closure (A ∪ B) := by
  intro x hx
  rcases hx with ⟨hxA, _hxB⟩
  -- Since `A ⊆ A ∪ B`, monotonicity of `closure` yields
  -- `closure A ⊆ closure (A ∪ B)`, and hence the desired membership.
  have hSub : A ⊆ A ∪ B := fun y hy => Or.inl hy
  have hCl : closure A ⊆ closure (A ∪ B) := closure_mono hSub
  exact hCl hxA

theorem P1_nonempty_iff_closureInterior_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) :
    A.Nonempty ↔ (closure (interior A)).Nonempty := by
  constructor
  · intro hA
    exact
      Topology.P1_nonempty_closureInterior (X := X) (A := A) hP1 hA
  · intro hCl
    exact
      nonempty_of_closureInterior_nonempty (X := X) (A := A) hCl

theorem closure_inter_eq_of_isClosed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∩ B) = A ∩ B := by
  have hClosed : IsClosed (A ∩ B) := hA.inter hB
  simpa [hClosed.closure_eq]

theorem interior_closure_subset_of_subset_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hB : IsClosed B) :
    interior (closure A) ⊆ B := by
  intro x hxInt
  have hclosure : closure A ⊆ B := by
    have h : closure A ⊆ closure B := closure_mono hAB
    simpa [hB.closure_eq] using h
  exact hclosure (interior_subset hxInt)

theorem closure_interior_empty {X : Type*} [TopologicalSpace X] :
    closure (interior (∅ : Set X)) = (∅ : Set X) := by
  simp

theorem interior_closure_interior_inter_subset_interior_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A ∩ interior B)) ⊆
      interior (closure (A ∩ B)) := by
  -- First, note that `interior A ∩ interior B ⊆ A ∩ B`.
  have h_subset : interior A ∩ interior B ⊆ A ∩ B := by
    intro x hx
    exact And.intro (interior_subset hx.1) (interior_subset hx.2)
  -- Taking closures preserves inclusions.
  have h_closure :
      closure (interior A ∩ interior B) ⊆ closure (A ∩ B) :=
    closure_mono h_subset
  -- Applying `interior_mono` yields the desired inclusion.
  exact interior_mono h_closure

theorem P1_union_closure {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A) (hB : Topology.P1 B) :
    Topology.P1 (closure (A ∪ B)) := by
  have hUnion : Topology.P1 (A ∪ B) :=
    Topology.P1_union (X := X) (A := A) (B := B) hA hB
  have hCl : Topology.P1 (closure (A ∪ B)) :=
    Topology.P1_imp_P1_closure (X := X) (A := A ∪ B) hUnion
  simpa using hCl

theorem P3_subset_closureInteriorClosure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 A) :
    A ⊆ closure (interior (closure A)) := by
  dsimp [Topology.P3] at hP3
  intro x hxA
  have hxInt : x ∈ interior (closure A) := hP3 hxA
  exact (subset_closure : interior (closure A) ⊆ closure (interior (closure A))) hxInt

theorem interior_closureInterior_subset_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior A) := by
  simpa using
    (interior_subset :
      interior (closure (interior A)) ⊆ closure (interior A))

theorem interior_nonempty_imp_interiorClosure_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : (interior A).Nonempty) :
    (interior (closure A)).Nonempty := by
  rcases hInt with ⟨x, hx⟩
  have hIncl : interior A ⊆ interior (closure A) :=
    interior_subset_interiorClosure (X := X) (A := A)
  exact ⟨x, hIncl hx⟩

theorem P2_nonempty_iff_closureInterior_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) :
    A.Nonempty ↔ (closure (interior A)).Nonempty := by
  constructor
  · intro hA
    exact
      Topology.P2_nonempty_closureInterior (X := X) (A := A) hP2 hA
  · intro hCl
    exact nonempty_of_closureInterior_nonempty (X := X) (A := A) hCl

theorem closure_nonempty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure A).Nonempty ↔ A.Nonempty := by
  constructor
  · intro hCl
    by_contra hA
    have hAeq : A = (∅ : Set X) :=
      Set.not_nonempty_iff_eq_empty.mp hA
    simpa [hAeq, closure_empty] using hCl
  · intro hA
    rcases hA with ⟨x, hxA⟩
    exact ⟨x, (subset_closure : A ⊆ closure A) hxA⟩

theorem closed_P2_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A ↔ interior A = A := by
  -- First relate `P2 A` to the openness of `A` via an existing equivalence.
  have hEquiv := Topology.closed_P2_iff_isOpen (X := X) (A := A) hA_closed
  constructor
  · intro hP2
    -- From `P2` we obtain that `A` is open.
    have hOpen : IsOpen A := (hEquiv).1 hP2
    -- For an open set, the interior is itself.
    simpa using hOpen.interior_eq
  · intro hIntEq
    -- The equality `interior A = A` shows that `A` is open.
    have hOpen : IsOpen A := by
      have hIntOpen : IsOpen (interior A) := isOpen_interior
      simpa [hIntEq] using hIntOpen
    -- Convert openness back to `P2` using the equivalence.
    exact (hEquiv).2 hOpen

theorem dense_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure A = (Set.univ : Set X)) :
    Topology.P1 (closure A) := by
  dsimp [Topology.P1]
  intro x _hx
  -- First, compute `interior (closure A) = univ`.
  have h_int : interior (closure A) = (Set.univ : Set X) := by
    simpa [h_dense, interior_univ]
  -- Consequently, `closure (interior (closure A)) = univ`.
  have h_cl : closure (interior (closure A)) = (Set.univ : Set X) := by
    simpa [h_int, closure_univ]
  -- The required membership is now trivial.
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_cl] using this

theorem interior_diff_subset_closure_diff_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B) ⊆ closure A \ closure B := by
  intro x hx
  -- `x` lies in `closure A` by an existing lemma.
  have hxClA : x ∈ closure A :=
    interior_diff_subset_closure_left (X := X) (A := A) (B := B) hx
  -- `x` is not in `closure B`, using another established lemma.
  have hxNotClB : x ∉ closure B := by
    have h := (interior_diff_subset (X := X) (A := A) (B := B)) hx
    exact h.2
  exact And.intro hxClA hxNotClB

theorem interior_closure_subset_closure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    interior (closure A) ⊆ closure B := by
  -- `interior (closure A)` is always contained in `closure A`.
  have h₁ : interior (closure A) ⊆ closure A := interior_subset
  -- Monotonicity of `closure` turns `A ⊆ B` into `closure A ⊆ closure B`.
  have h₂ : closure A ⊆ closure B := closure_mono hAB
  -- Combine the two inclusions to obtain the desired result.
  exact Set.Subset.trans h₁ h₂

theorem closureInterior_iUnion_subset_closureInterior_iUnion
    {X ι : Type*} [TopologicalSpace X] (A : ι → Set X) :
    (⋃ i, closure (interior (A i))) ⊆ closure (interior (⋃ i, A i)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `interior (A i)` is contained in `interior (⋃ i, A i)`
  have h_int_subset : interior (A i) ⊆ interior (⋃ j, A j) := by
    have h_subset : A i ⊆ ⋃ j, A j := by
      intro y hy; exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact interior_mono h_subset
  -- Taking closures preserves inclusions
  have h_closure_subset :
      closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) :=
    closure_mono h_int_subset
  exact h_closure_subset hx_i

theorem isClosed_closure_inter {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed (closure A ∩ closure B) := by
  simpa using (isClosed_closure.inter isClosed_closure)

theorem P2_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) :
    A ⊆ closure A := by
  intro x hxA
  -- From `P2`, we have `x ∈ interior (closure (interior A))`.
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  -- The interior is contained in the closure of the same set.
  have hIntSubset : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  have hxClInt : x ∈ closure (interior A) := hIntSubset hxInt
  -- Finally, `closure (interior A)` is contained in `closure A`.
  have hClSubset : closure (interior A) ⊆ closure A :=
    closure_interior_subset_closure (X := X) (A := A)
  exact hClSubset hxClInt

theorem closure_inter_interior_subset_closureInterior_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ interior B) ⊆ closure (interior B) := by
  have h : A ∩ interior B ⊆ interior B := by
    intro x hx
    exact hx.2
  exact closure_mono h

theorem closure_interInterior_subset_closureInterior_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∩ interior B) ⊆ closure (interior (A ∩ B)) := by
  have h : interior A ∩ interior B ⊆ interior (A ∩ B) :=
    interior_inter_interior_subset_interior_inter (X := X) (A := A) (B := B)
  exact closure_mono h

theorem P2_imp_closure_subset_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) :
    closure A ⊆ closure (interior (closure A)) := by
  -- First, upgrade `P2 A` to `P3 A`.
  have hP3 : Topology.P3 A :=
    Topology.P2_imp_P3 (X := X) (A := A) hP2
  -- Then apply the established result for `P3 A`.
  exact
    Topology.P3_imp_closure_subset_closureInteriorClosure
      (X := X) (A := A) hP3

theorem interior_iInter_subset_iInter_interior
    {X ι : Type*} [TopologicalSpace X] (A : ι → Set X) :
    interior (Set.iInter A) ⊆ Set.iInter (fun i => interior (A i)) := by
  classical
  intro x hx
  rcases (Set.mem_interior).1 hx with ⟨U, hU_open, hU_sub, hxU⟩
  apply Set.mem_iInter.2
  intro i
  have hU_sub_i : U ⊆ A i := by
    intro y hy
    have h_mem : y ∈ Set.iInter A := hU_sub hy
    exact (Set.mem_iInter.1 h_mem) i
  exact
    (Set.mem_interior).2 ⟨U, hU_open, hU_sub_i, hxU⟩

theorem closure_iInter_subset_iInter_closure {X ι : Type*} [TopologicalSpace X]
    (A : ι → Set X) :
    closure (⋂ i, A i) ⊆ ⋂ i, closure (A i) := by
  intro x hx
  apply Set.mem_iInter.2
  intro i
  -- `⋂ i, A i` is contained in `A i`.
  have h_subset : (⋂ i, A i) ⊆ A i := Set.iInter_subset _ i
  -- Taking closures preserves inclusions.
  have h_closure : closure (⋂ i, A i) ⊆ closure (A i) := closure_mono h_subset
  exact h_closure hx

theorem closure_inter_subset_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B) ⊆ closure A := by
  have h : A ∩ B ⊆ A := Set.inter_subset_left
  exact closure_mono h

theorem closure_union_eq_of_isClosed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∪ B) = A ∪ B := by
  calc
    closure (A ∪ B) = closure A ∪ closure B := by
      simpa using
        (closure_union : closure (A ∪ B) = closure A ∪ closure B)
    _ = A ∪ B := by
      simpa [hA.closure_eq, hB.closure_eq]

theorem interior_inter_eq_of_isOpen {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∩ B) = A ∩ B := by
  have h_open : IsOpen (A ∩ B) := IsOpen.inter hA hB
  simpa using h_open.interior_eq

theorem interior_inter_closure_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∩ closure B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hxIntA, hxClB⟩
  -- We will use the neighbourhood characterization of the closure.
  -- Reformulate the goal using `mem_closure_iff`.
  have : (∀ U : Set X, IsOpen U → x ∈ U → (U ∩ (A ∩ B)).Nonempty) := by
    intro U hU_open hxU
    -- Consider the open set `V = U ∩ interior A`, which also contains `x`.
    let V : Set X := U ∩ interior A
    have hV_open : IsOpen V := hU_open.inter isOpen_interior
    have hxV : x ∈ V := And.intro hxU hxIntA
    -- Because `x ∈ closure B`, the neighbourhood `V` meets `B`.
    have hNon : (V ∩ B).Nonempty :=
      (mem_closure_iff).1 hxClB V hV_open hxV
    -- Any point in `V ∩ B` lies in `U ∩ (A ∩ B)`.
    rcases hNon with ⟨y, hyV, hyB⟩
    have hyU : y ∈ U := hyV.1
    have hyIntA : y ∈ interior A := hyV.2
    have hyA : y ∈ A := interior_subset hyIntA
    exact ⟨y, And.intro hyU (And.intro hyA hyB)⟩
  -- Conclude that `x ∈ closure (A ∩ B)`.
  exact (mem_closure_iff).2 this

theorem closure_interInterior_subset_closureInterior_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∩ B) ⊆ closure (interior A) := by
  -- `interior A ∩ B` is contained in `interior A`
  have h : interior A ∩ B ⊆ interior A := by
    intro x hx
    exact hx.1
  -- Taking closures preserves inclusions
  exact closure_mono h

theorem P2_subset_closure_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP2 : Topology.P2 A) (hAB : A ⊆ B) :
    A ⊆ closure B := by
  intro x hxA
  -- Step 1: use `P2` to place `x` in `interior (closure (interior A))`.
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  -- Step 2: enlarge the set step by step, ending in `closure B`.
  -- `interior (closure (interior A)) ⊆ closure (interior A)`.
  have hxClIntA : x ∈ closure (interior A) :=
    (interior_subset : interior (closure (interior A)) ⊆
        closure (interior A)) hxInt
  -- `closure (interior A) ⊆ closure (interior B)` because `A ⊆ B`.
  have h₁ : closure (interior A) ⊆ closure (interior B) := by
    have hInt : interior A ⊆ interior B := interior_mono hAB
    exact closure_mono hInt
  have hxClIntB : x ∈ closure (interior B) := h₁ hxClIntA
  -- Finally, `closure (interior B) ⊆ closure B`.
  have h₂ : closure (interior B) ⊆ closure B := by
    have hIntB : interior B ⊆ B := interior_subset
    exact closure_mono hIntB
  exact h₂ hxClIntB

theorem interior_closure_univ {X : Type*} [TopologicalSpace X] :
    interior (closure (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [closure_univ, interior_univ]

theorem interior_closure_iInter_subset_iInter_interior_closure
    {X ι : Type*} [TopologicalSpace X] (A : ι → Set X) :
    interior (closure (⋂ i, A i)) ⊆ ⋂ i, interior (closure (A i)) := by
  intro x hx
  -- For each index `i`, show that `x` lies in `interior (closure (A i))`.
  have h_mem : ∀ i, x ∈ interior (closure (A i)) := by
    intro i
    -- `⋂ i, A i` is contained in `A i`
    have h_subset : (⋂ j, A j) ⊆ A i := Set.iInter_subset _ i
    -- Taking closures preserves inclusions
    have h_closure : closure (⋂ j, A j) ⊆ closure (A i) :=
      closure_mono h_subset
    -- Interiority is monotone
    have h_interior : interior (closure (⋂ j, A j)) ⊆ interior (closure (A i)) :=
      interior_mono h_closure
    exact h_interior hx
  exact Set.mem_iInter.2 h_mem

theorem P3_imp_interior_closureInteriorClosure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP3 : Topology.P3 A) :
    interior (closure (interior (closure A))) = interior (closure A) := by
  have h :=
    Topology.P3_imp_closureInteriorClosure_eq_closure (X := X) (A := A) hP3
  simpa [h]

theorem closure_subset_of_subset_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    (closure A ⊆ interior B) → closure A ⊆ B := by
  intro hSub
  intro x hxClA
  have hxIntB : x ∈ interior B := hSub hxClA
  exact interior_subset hxIntB

theorem closure_interInterior_subset_closure_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior A ∩ interior B) ⊆ closure (A ∩ B) := by
  -- `interior A ∩ interior B` is contained in `A ∩ B`
  have h_subset : interior A ∩ interior B ⊆ A ∩ B := by
    intro x hx
    exact And.intro (interior_subset hx.1) (interior_subset hx.2)
  -- Taking closures preserves inclusions
  exact closure_mono h_subset

theorem P2_of_subset_and_subset_interiorClosure {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B)
    (hBsubset : B ⊆ interior (closure (interior A))) :
    Topology.P2 B := by
  dsimp [Topology.P2] at *
  intro x hxB
  -- From the hypothesis `hBsubset`, the point `x` already lies in
  -- `interior (closure (interior A))`.
  have hx₁ : x ∈ interior (closure (interior A)) := hBsubset hxB
  -- Since `A ⊆ B`, we have `interior A ⊆ interior B`.
  have hInt : interior A ⊆ interior B := interior_mono hAB
  -- Taking closures preserves inclusions.
  have hCl : closure (interior A) ⊆ closure (interior B) :=
    closure_mono hInt
  -- Applying `interior_mono` yields the desired containment between interiors.
  have hIncl :
      interior (closure (interior A)) ⊆
        interior (closure (interior B)) :=
    interior_mono hCl
  -- Conclude that `x ∈ interior (closure (interior B))`.
  exact hIncl hx₁

theorem closure_diff_subset_closureDiff_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hB : IsClosed B) :
    closure A \ B ⊆ closure (A \ B) := by
  intro x hx
  rcases hx with ⟨hxClA, hxNotB⟩
  -- Use the neighborhood characterization of `closure`.
  have h :
      ∀ U : Set X, IsOpen U → x ∈ U → (U ∩ (A \ B)).Nonempty := by
    intro U hU_open hxU
    -- The complement of the closed set `B` is open.
    have hOpenCompl : IsOpen (Bᶜ) := by
      simpa using (isOpen_compl_iff).2 hB
    -- Intersect the neighborhood `U` with `Bᶜ`, which is still open.
    have hV_open : IsOpen (U ∩ Bᶜ) := hU_open.inter hOpenCompl
    have hxV : x ∈ U ∩ Bᶜ := And.intro hxU hxNotB
    -- Since `x ∈ closure A`, this open set meets `A`.
    have hNon : (U ∩ Bᶜ ∩ A).Nonempty :=
      (mem_closure_iff).1 hxClA (U ∩ Bᶜ) hV_open hxV
    -- Repackage the witness to lie in `U ∩ (A \ B)`.
    rcases hNon with ⟨y, hy⟩
    rcases hy with ⟨⟨hyU, hyNotB⟩, hyA⟩
    have hyNotB' : y ∉ B := by
      simpa using hyNotB
    exact ⟨y, And.intro hyU (And.intro hyA hyNotB')⟩
  -- Conclude that `x ∈ closure (A \ B)`.
  exact (mem_closure_iff).2 h

theorem closure_interInterior_subset_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∩ interior B) ⊆ closure B := by
  -- Since `interior B ⊆ B`, the set `A ∩ interior B` is contained in `B`.
  have h : A ∩ interior B ⊆ B := by
    intro x hx
    exact (interior_subset : interior B ⊆ B) hx.2
  -- Taking closures preserves inclusions.
  exact closure_mono h

theorem interior_eq_self_of_closed_iff_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    interior A = A ↔ IsOpen A := by
  constructor
  · intro hInt
    have hOpenInt : IsOpen (interior A) := isOpen_interior
    simpa [hInt] using hOpenInt
  · intro hOpen
    simpa using hOpen.interior_eq

theorem closure_inter_subset_right {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B) ⊆ closure B := by
  have h : A ∩ B ⊆ B := Set.inter_subset_right
  exact closure_mono h

theorem closure_interInterior_inter_subset_inter_closureInterior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∩ interior B) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  have hxA : x ∈ closure (interior A) := by
    -- `interior A ∩ interior B` is contained in `interior A`.
    have h : interior A ∩ interior B ⊆ interior A := by
      intro y hy; exact hy.1
    exact (closure_mono h) hx
  have hxB : x ∈ closure (interior B) := by
    -- `interior A ∩ interior B` is contained in `interior B`.
    have h : interior A ∩ interior B ⊆ interior B := by
      intro y hy; exact hy.2
    exact (closure_mono h) hx
  exact And.intro hxA hxB



theorem interior_iUnion_subset_interior_iUnion {X ι : Type*} [TopologicalSpace X]
    (A : ι → Set X) :
    (⋃ i, interior (A i)) ⊆ interior (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxIntAi⟩
  have h_sub : A i ⊆ ⋃ j, A j := by
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  have h_int : interior (A i) ⊆ interior (⋃ j, A j) :=
    interior_mono h_sub
  exact h_int hxIntAi

theorem interior_compl_eq_compl_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (Aᶜ) = (closure A)ᶜ := by
  classical
  ext x
  constructor
  · -- `x ∈ interior (Aᶜ) → x ∉ closure A`
    intro hx
    -- Assume, for contradiction, that `x ∈ closure A`
    have h : x ∉ closure A := by
      intro hxCl
      -- Obtain an open neighbourhood `U` of `x` contained in `Aᶜ`
      rcases (Set.mem_interior).1 hx with ⟨U, hU_open, hU_sub, hxU⟩
      -- Since `x ∈ closure A`, `U` meets `A`
      have hNon : (U ∩ A).Nonempty :=
        (mem_closure_iff).1 hxCl U hU_open hxU
      rcases hNon with ⟨y, hyU, hyA⟩
      -- But `U ⊆ Aᶜ`, contradiction
      have : y ∈ Aᶜ := hU_sub hyU
      exact this hyA
    exact h
  · -- `x ∉ closure A → x ∈ interior (Aᶜ)`
    intro hx
    -- The set `V = (closure A)ᶜ` is open and contains `x`
    have hV_open : IsOpen ((closure A)ᶜ) := (isOpen_compl_iff).2 isClosed_closure
    have hxV : x ∈ (closure A)ᶜ := hx
    -- Show `V ⊆ Aᶜ`
    have hV_sub : (closure A)ᶜ ⊆ Aᶜ := by
      intro y hy
      by_cases hA : y ∈ A
      · have : (y : X) ∈ closure A := subset_closure hA
        exact (hy this).elim
      · exact hA
    -- Conclude that `x` lies in the interior of `Aᶜ`
    exact
      (Set.mem_interior).2 ⟨(closure A)ᶜ, hV_open, hV_sub, hxV⟩

theorem closure_closure_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (closure (interior A)) = closure (interior A) := by
  simpa [closure_closure]

theorem closure_interInterior_subset_closureInterior_and_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∩ B) ⊆ closure (interior A) ∩ closure B := by
  intro x hx
  have hx₁ : x ∈ closure (interior A) := by
    -- `interior A ∩ B` is contained in `interior A`
    have h_subset : interior A ∩ B ⊆ interior A := by
      intro y hy
      exact hy.1
    exact (closure_mono h_subset) hx
  have hx₂ : x ∈ closure B := by
    -- `interior A ∩ B` is contained in `B`
    have h_subset : interior A ∩ B ⊆ B := by
      intro y hy
      exact hy.2
    exact (closure_mono h_subset) hx
  exact And.intro hx₁ hx₂

theorem Set.compl_compl {α : Type*} (s : Set α) : (sᶜᶜ : Set α) = s := by
  ext x
  by_cases h : x ∈ s <;> simp [h]



theorem closure_interior_closure_interior_subset_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) ⊆
      closure (interior (closure A)) := by
  -- We already have the inclusion between the interiors.
  have h :
      interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_closure_interior_subset_interior_closure (X := X) (A := A)
  -- Taking closures preserves inclusions.
  exact closure_mono h

theorem closure_compl_eq_compl_interior {α : Type*} [TopologicalSpace α]
    {s : Set α} :
    closure (sᶜ) = (interior s)ᶜ := by
  classical
  -- First, apply the known relation to the complement `sᶜ`.
  have h : interior s = (closure (sᶜ))ᶜ := by
    simpa [Set.compl_compl s] using
      (interior_compl_eq_compl_closure (A := sᶜ))
  -- Taking complements of both sides yields the desired equality.
  have : closure (sᶜ) = (interior s)ᶜ := by
    have h' := congrArg Set.compl h
    simpa [Set.compl_compl] using h'
  simpa using this

theorem closure_interior_compl_eq_compl_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (Aᶜ)) = (interior (closure A))ᶜ := by
  have h₁ : interior (Aᶜ) = (closure A)ᶜ := by
    simpa using
      (interior_compl_eq_compl_closure (X := X) (A := A))
  have h₂ : closure ((closure A)ᶜ) = (interior (closure A))ᶜ := by
    simpa using
      (closure_compl_eq_compl_interior (α := X) (s := closure A))
  simpa [h₁] using h₂

theorem compl_closure_compl_eq_interior {α : Type*} [TopologicalSpace α] {s : Set α} :
    (closure (sᶜ))ᶜ = interior s := by
  have h := closure_compl_eq_compl_interior (α := α) (s := s)
  simpa [Set.compl_compl] using congrArg Set.compl h

theorem interior_diff_closed_eq_self {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsClosed B) :
    interior (A \ B) = A \ B := by
  have h := interior_diff_eq_self_diff_closure (X := X) (A := A) (B := B) hA
  simpa [hB.closure_eq] using h

theorem interior_closure_interInterior_subset_interior_closure_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A ∩ B)) ⊆ interior (closure B) := by
  -- `interior A ∩ B` is contained in `B`.
  have h_subset : interior A ∩ B ⊆ B := by
    intro x hx
    exact hx.2
  -- Taking closures preserves inclusions.
  have h_closure : closure (interior A ∩ B) ⊆ closure B :=
    closure_mono h_subset
  -- Applying `interior_mono` yields the desired inclusion.
  exact interior_mono h_closure

theorem dense_imp_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure A = (Set.univ : Set X)) :
    Topology.P2 (closure A) := by
  -- The set `closure A` is `univ`, hence open.
  have hOpen : IsOpen (closure A) := by
    simpa [h_dense] using isOpen_univ
  -- Openness of `closure A` immediately yields `P2`.
  exact isOpen_closure_imp_P2_closure (X := X) (A := A) hOpen

theorem closure_eq_compl_interior_compl {α : Type*} [TopologicalSpace α] {s : Set α} :
    closure s = (interior (sᶜ))ᶜ := by
  have h : interior (sᶜ) = (closure s)ᶜ :=
    interior_compl_eq_compl_closure (X := α) (A := s)
  calc
    closure s = ((closure s)ᶜ)ᶜ := by
      simpa using (Set.compl_compl (closure s))
    _ = (interior (sᶜ))ᶜ := by
      simpa [h]

theorem closureInterior_diff_subset_closure_diff_left {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B)) ⊆ closure A \ interior B := by
  intro x hx
  -- `x` lies in `closure A`
  have hxClA : x ∈ closure A := by
    -- `interior (A \ B)` is contained in `A`
    have h_sub : interior (A \ B) ⊆ A := by
      intro y hy
      have h_mem : y ∈ A \ B := interior_subset hy
      exact h_mem.1
    exact (closure_mono h_sub) hx
  -- `x` is *not* in `interior B`
  have hxNotIntB : x ∉ interior B := by
    intro hxIntB
    -- `interior B` is an open neighbourhood of `x`
    have h_non : (interior B ∩ interior (A \ B)).Nonempty :=
      (mem_closure_iff).1 hx (interior B) isOpen_interior hxIntB
    rcases h_non with ⟨y, ⟨hyIntB, hyIntDiff⟩⟩
    -- Points of `interior (A \ B)` are outside `B`
    have hyB : y ∈ B := interior_subset hyIntB
    have hyNotB : y ∉ B := by
      have h_mem : y ∈ A \ B := interior_subset hyIntDiff
      exact h_mem.2
    exact hyNotB hyB
  exact And.intro hxClA hxNotIntB

theorem interior_closure_compl_eq_compl_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (Aᶜ)) = (closure (interior A))ᶜ := by
  calc
    interior (closure (Aᶜ))
        = interior ((interior A)ᶜ) := by
          simpa [closure_compl_eq_compl_interior (α := X) (s := A)]
    _ = (closure (interior A))ᶜ := by
          simpa using
            (interior_compl_eq_compl_closure (X := X) (A := interior A))



theorem closure_inter_interior_compl_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ∩ interior (Aᶜ) = (∅ : Set X) := by
  -- Rewrite `interior (Aᶜ)` as the complement of `closure A`.
  have h : interior (Aᶜ) = (closure A)ᶜ :=
    interior_compl_eq_compl_closure (X := X) (A := A)
  calc
    closure A ∩ interior (Aᶜ)
        = closure A ∩ (closure A)ᶜ := by
          simpa [h]
    _ = (∅ : Set X) := by
          simpa using Set.inter_compl_self (closure A)



theorem interior_inter_closure_compl_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ∩ closure (Aᶜ) = (∅ : Set X) := by
  have h : closure (Aᶜ) = (interior A)ᶜ := by
    simpa using closure_compl_eq_compl_interior (α := X) (s := A)
  calc
    interior A ∩ closure (Aᶜ)
        = interior A ∩ (interior A)ᶜ := by
          simpa [h]
    _ = (∅ : Set X) := by
          simpa using Set.inter_compl_self (interior A)

theorem closure_interInterior_subset_inter_closure'
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ interior B) ⊆ closure A ∩ closure B := by
  intro x hx
  -- `A ∩ interior B` is contained in `A`.
  have hxA : x ∈ closure A := by
    have hSub : A ∩ interior B ⊆ A := by
      intro y hy
      exact hy.1
    exact (closure_mono hSub) hx
  -- `A ∩ interior B` is also contained in `B` (because `interior B ⊆ B`).
  have hxB : x ∈ closure B := by
    have hSub : A ∩ interior B ⊆ B := by
      intro y hy
      exact (interior_subset : interior B ⊆ B) hy.2
    exact (closure_mono hSub) hx
  exact And.intro hxA hxB

theorem interior_inter_closure_eq_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ∩ closure A = interior A := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.1
  · intro x hxInt
    have hxCl : x ∈ closure A := subset_closure (interior_subset hxInt)
    exact And.intro hxInt hxCl

theorem closure_union_interior_complement_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A ∪ interior (Aᶜ) = (Set.univ : Set X) := by
  have h : interior (Aᶜ : Set X) = (closure A)ᶜ :=
    interior_compl_eq_compl_closure (X := X) (A := A)
  calc
    closure A ∪ interior (Aᶜ)
        = closure A ∪ (closure A)ᶜ := by
          simpa [h]
    _ = (Set.univ : Set X) := by
          simpa using Set.union_compl_self (closure A)

theorem interior_union_closure_complement_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (A : Set X) ∪ closure (Aᶜ) = (Set.univ : Set X) := by
  classical
  have h : closure (Aᶜ : Set X) = (interior A)ᶜ :=
    closure_compl_eq_compl_interior (α := X) (s := A)
  calc
    interior A ∪ closure (Aᶜ)
        = interior A ∪ (interior A)ᶜ := by
          simpa [h]
    _ = (Set.univ : Set X) := by
          simpa using Set.union_compl_self (interior A)

theorem interior_inter_interior_compl_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ∩ interior (Aᶜ) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxA, hxAc⟩
    have hA : x ∈ A := interior_subset hxA
    have hAc : x ∈ Aᶜ := interior_subset hxAc
    have : False := hAc hA
    exact this.elim
  · exact Set.empty_subset _

theorem closure_interInterior_subset_closure_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∩ B) ⊆ closure A := by
  -- The set `interior A ∩ B` is contained in `A`
  have h : interior A ∩ B ⊆ A := by
    intro x hx
    exact (interior_subset : interior A ⊆ A) hx.1
  -- Taking closures preserves inclusions
  exact closure_mono h

theorem interior_eq_self_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A = A ↔ IsOpen A := by
  constructor
  · intro h_eq
    -- The interior of any set is open; rewrite using the hypothesis.
    simpa [h_eq] using (isOpen_interior : IsOpen (interior A))
  · intro h_open
    -- For an open set, the interior is itself.
    simpa using h_open.interior_eq

theorem closure_diff_closure_subset_closureDiff {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure A \ closure B ⊆ closure (A \ B) := by
  intro x hx
  rcases hx with ⟨hxA, hxNotB⟩
  -- To show that `x` is in `closure (A \ B)`, we use the neighborhood
  -- characterization of the closure.
  have h :
      ∀ U : Set X, IsOpen U → x ∈ U → (U ∩ (A \ B)).Nonempty := by
    intro U hU_open hxU
    -- Consider the open set `V = U ∩ (closure B)ᶜ`, which avoids `closure B`.
    have hOpenCompl : IsOpen ((closure B)ᶜ) := by
      have hClosed : IsClosed (closure B) := isClosed_closure
      simpa using (isOpen_compl_iff).2 hClosed
    have hV_open : IsOpen (U ∩ (closure B)ᶜ) := hU_open.inter hOpenCompl
    have hxV : x ∈ U ∩ (closure B)ᶜ := And.intro hxU hxNotB
    -- Because `x ∈ closure A`, the set `V` meets `A`.
    have hNon : ((U ∩ (closure B)ᶜ) ∩ A).Nonempty :=
      (mem_closure_iff).1 hxA (U ∩ (closure B)ᶜ) hV_open hxV
    -- Any such point of intersection lies in `U ∩ (A \ B)`.
    rcases hNon with ⟨y, ⟨hyU, hyNotClB⟩, hyA⟩
    -- Show that `y ∉ B`.
    have hyNotB : y ∉ B := by
      intro hyB
      have : (y : X) ∈ closure B := subset_closure hyB
      exact hyNotClB this
    exact ⟨y, And.intro hyU (And.intro hyA hyNotB)⟩
  -- Conclude that `x ∈ closure (A \ B)`.
  exact (mem_closure_iff).2 h

theorem closure_closure_interior_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (closure (interior (closure A))) = closure (interior (closure A)) := by
  simpa [closure_closure]

theorem interior_subset_interior_union_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior A ⊆ interior (A ∪ B) := by
  -- The set `A` is contained in `A ∪ B`.
  have h : A ⊆ A ∪ B := by
    intro x hx
    exact Or.inl hx
  -- Monotonicity of `interior` yields the desired inclusion.
  exact interior_mono h

theorem interior_closure_interInterior_subset_inter_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ interior B)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- First, show `x ∈ interior (closure A)`.
  have hxA : x ∈ interior (closure A) := by
    -- Because `A ∩ interior B ⊆ A`, their closures are related.
    have h_sub : closure (A ∩ interior B) ⊆ closure A := by
      have h : A ∩ interior B ⊆ A := by
        intro y hy; exact hy.1
      exact closure_mono h
    -- Apply monotonicity of `interior`.
    have h_int : interior (closure (A ∩ interior B)) ⊆ interior (closure A) :=
      interior_mono h_sub
    exact h_int hx
  -- Next, show `x ∈ interior (closure B)`.
  have hxB : x ∈ interior (closure B) := by
    -- Since `interior B ⊆ B`, we get another inclusion of closures.
    have h_sub : closure (A ∩ interior B) ⊆ closure B := by
      have h : A ∩ interior B ⊆ B := by
        intro y hy; exact (interior_subset : interior B ⊆ B) hy.2
      exact closure_mono h
    -- Again use monotonicity of `interior`.
    have h_int : interior (closure (A ∩ interior B)) ⊆ interior (closure B) :=
      interior_mono h_sub
    exact h_int hx
  -- Combine the two memberships.
  exact And.intro hxA hxB

theorem closure_inter_closure_compl_eq_closure_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ∩ closure (Aᶜ) = closure A \ interior A := by
  classical
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxClA, hxClAc⟩
    have hEq : closure (Aᶜ) = (interior A)ᶜ :=
      closure_compl_eq_compl_interior (α := X) (s := A)
    have hNotIntA : x ∉ interior A := by
      have : x ∈ (interior A)ᶜ := by
        simpa [hEq] using hxClAc
      simpa using this
    exact And.intro hxClA hNotIntA
  · intro hx
    rcases hx with ⟨hxClA, hNotIntA⟩
    have hEq : closure (Aᶜ) = (interior A)ᶜ :=
      closure_compl_eq_compl_interior (α := X) (s := A)
    have hxClAc : x ∈ closure (Aᶜ) := by
      have : x ∈ (interior A)ᶜ := hNotIntA
      simpa [hEq] using this
    exact And.intro hxClA hxClAc



theorem closure_eq_self_iff_isClosed_set {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = A ↔ IsClosed A := by
  constructor
  · intro h_eq
    -- `closure A` is always closed, and it coincides with `A`.
    have h_closed : IsClosed (closure (A : Set X)) := isClosed_closure
    simpa [h_eq] using h_closed
  · intro h_closed
    -- A closed set is equal to its closure.
    simpa using h_closed.closure_eq

theorem interior_union_eq_union_interiors_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∪ B) = interior A ∪ interior B := by
  -- `A` and `B` are open, so their interiors coincide with themselves.
  have hIntA : interior A = A := hA.interior_eq
  have hIntB : interior B = B := hB.interior_eq
  -- The union of two open sets is open.
  have hOpenUnion : IsOpen (A ∪ B) := hA.union hB
  -- Hence the interior of the union is the union itself.
  have hIntUnion : interior (A ∪ B) = A ∪ B := hOpenUnion.interior_eq
  -- Rewrite everything in terms of `interior`.
  simpa [hIntUnion, hIntA, hIntB]

theorem interior_interior_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (interior (closure A)) = interior (closure A) := by
  simpa [interior_interior]

theorem interior_inter_subset_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B) ⊆ interior A := by
  -- `A ∩ B` is contained in `A`, hence their interiors satisfy the same relation.
  exact interior_mono (Set.inter_subset_left : A ∩ B ⊆ A)