

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 A := by
  intro hA
  dsimp [Topology.P2] at hA
  dsimp [Topology.P1]
  exact hA.trans interior_subset

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P3 A := by
  intro hA
  dsimp [Topology.P2, Topology.P3] at *
  exact hA.trans (interior_mono (closure_mono interior_subset))

theorem interior_satisfies_P1 {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) := by
  dsimp [Topology.P1]
  simpa using (subset_closure : interior A ⊆ closure (interior A))

theorem interior_satisfies_P2 {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior A) := by
  dsimp [Topology.P2]
  have h : interior A ⊆ interior (closure (interior A)) :=
    interior_maximal subset_closure isOpen_interior
  simpa [interior_interior] using h

theorem interior_satisfies_P3 {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior A) := by
  have h : Topology.P2 (interior A) := interior_satisfies_P2 A
  exact P2_implies_P3 h

theorem interior_closure_interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  exact interior_mono (closure_mono interior_subset)

theorem open_satisfies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 A := by
  dsimp [Topology.P3]
  exact interior_maximal subset_closure hA

theorem open_satisfies_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 A := by
  dsimp [Topology.P2]
  have h : interior (interior A) ⊆ interior (closure (interior A)) :=
    interior_mono subset_closure
  simpa [interior_interior, hA.interior_eq] using h

theorem open_satisfies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A := by
  dsimp [Topology.P1]
  simpa [hA.interior_eq] using (subset_closure : interior A ⊆ closure (interior A))

theorem P3_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 A ↔ Topology.P2 A := by
  have h₁ : Topology.P3 A → Topology.P2 A := by
    intro h3
    dsimp [Topology.P3, Topology.P2] at h3 ⊢
    simpa [hA.interior_eq] using h3
  have h₂ : Topology.P2 A → Topology.P3 A := by
    intro h2
    exact P2_implies_P3 h2
  exact ⟨h₁, h₂⟩

theorem P3_iff_P2_of_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior A) ↔ Topology.P2 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  simpa using (Topology.P3_iff_P2_of_isOpen (A := interior A) hOpen)

theorem closure_interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure A := by
  exact closure_mono interior_subset

theorem interior_closure_satisfies_P2 {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  simpa using (Topology.open_satisfies_P2 (A := interior (closure A)) hOpen)

theorem interior_closure_interior_satisfies_P3
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure (interior A))) := by
  have hP2 : Topology.P2 (interior (closure (interior A))) :=
    Topology.interior_closure_satisfies_P2 (A := interior A)
  exact Topology.P2_implies_P3 hP2

theorem interior_closure_satisfies_P3 {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure A)) := by
  have hP2 : Topology.P2 (interior (closure A)) :=
    Topology.interior_closure_satisfies_P2 (A := A)
  exact Topology.P2_implies_P3 hP2

theorem closure_open_satisfies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) : Topology.P3 A := by
  dsimp [Topology.P3]
  have hInt_eq : interior (closure (A : Set X)) = closure A := hOpen.interior_eq
  have hSub : (A : Set X) ⊆ closure A := subset_closure
  simpa [hInt_eq] using hSub

theorem interior_closure_interior_satisfies_P1 {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (interior A))) := by
  dsimp [Topology.P1]
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  simpa [hOpen.interior_eq] using
    (subset_closure :
      interior (closure (interior A)) ⊆ closure (interior (closure (interior A))))

theorem P3_closure_iff_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) ↔ IsOpen (closure A) := by
  constructor
  · intro hP3
    dsimp [Topology.P3] at hP3
    have h₁ : closure (A : Set X) ⊆ interior (closure A) := by
      simpa [closure_closure] using hP3
    have h₂ : interior (closure A) ⊆ closure A := interior_subset
    have hEq : interior (closure A) = closure A := subset_antisymm h₂ h₁
    have hOpenInt : IsOpen (interior (closure A)) := isOpen_interior
    simpa [hEq] using hOpenInt
  · intro hOpen
    dsimp [Topology.P3]
    simpa [closure_closure, hOpen.interior_eq]

theorem interior_closure_satisfies_P1 {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (A : Set X))) := by
  dsimp [Topology.P1]
  simpa using
    (subset_closure :
      interior (closure (A : Set X)) ⊆ closure (interior (closure A)))

theorem P3_iff_open_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) : Topology.P3 A ↔ IsOpen A := by
  simpa [hA.closure_eq] using
    (Topology.P3_closure_iff_open_closure (A := A))

theorem P3_closure_interior_iff_open_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 (closure (interior (A : Set X))) ↔ IsOpen (closure (interior A)) := by
  simpa using
    (Topology.P3_closure_iff_open_closure (A := interior A))

theorem interior_closure_interior_closure_satisfies_P2
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (closure (interior (closure A)))) := by
  simpa using
    (Topology.interior_closure_satisfies_P2 (A := interior (closure A)))

theorem P1_iff_closure_interior_eq_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) ↔ closure (interior A) = closure A := by
  constructor
  · intro hA
    have h₁ : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    have h₂ : closure A ⊆ closure (interior A) := by
      have h := closure_mono hA
      simpa [closure_closure] using h
    exact subset_antisymm h₁ h₂
  · intro hEq
    dsimp [Topology.P1]
    have h : (A : Set X) ⊆ closure A := subset_closure
    simpa [hEq] using h

theorem interior_closure_interior_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior A) := by
  simpa using (interior_subset : interior (closure (interior A)) ⊆ closure (interior A))

theorem P2_iff_open_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) : Topology.P2 A ↔ IsOpen A := by
  constructor
  · intro hP2
    have hP3 : Topology.P3 A := Topology.P2_implies_P3 hP2
    exact (Topology.P3_iff_open_of_closed (A := A) hA).1 hP3
  · intro hOpen
    exact Topology.open_satisfies_P2 (A := A) hOpen

theorem P3_closure_interior_closure_iff_open_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior (closure (A : Set X))))
      ↔ IsOpen (closure (interior (closure A))) := by
  simpa using
    (Topology.P3_closure_iff_open_closure
      (A := interior (closure (A : Set X))))

theorem P1_closure_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) → Topology.P1 (closure (A : Set X)) := by
  intro hA
  dsimp [Topology.P1] at hA ⊢
  -- First, lift the inclusion to the closures
  have h₁ : closure (A : Set X) ⊆ closure (interior A) := by
    simpa [closure_closure] using (closure_mono hA)
  -- Next, use monotonicity of interior and closure
  have h₂ : closure (interior A) ⊆ closure (interior (closure (A : Set X))) := by
    have h : interior A ⊆ interior (closure (A : Set X)) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono h
  exact h₁.trans h₂

theorem P3_iff_P2_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P3 (A : Set X) ↔ Topology.P2 A := by
  have h₁ := Topology.P3_iff_open_of_closed (A := A) hA
  have h₂ := Topology.P2_iff_open_of_closed (A := A) hA
  simpa using (h₁.trans h₂.symm)

theorem closure_interior_satisfies_P1 {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior (A : Set X))) := by
  have hP1 : Topology.P1 (interior A) := Topology.interior_satisfies_P1 (A := A)
  have hP1' : Topology.P1 (closure (interior A)) :=
    Topology.P1_closure_of_P1 (A := interior A) hP1
  simpa using hP1'

theorem P1_iff_closure_interior_eq_self_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed (A : Set X)) :
    Topology.P1 (A : Set X) ↔ closure (interior A) = A := by
  simpa [hA.closure_eq] using
    (Topology.P1_iff_closure_interior_eq_closure (A := A))

theorem P2_implies_closure_interior_eq_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → closure (interior A) = closure A := by
  intro hP2
  -- First, derive P1 from P2
  have hP1 : Topology.P1 (A : Set X) := Topology.P2_implies_P1 hP2
  -- Use the equivalence established for P1
  exact (Topology.P1_iff_closure_interior_eq_closure (A := A)).1 hP1

theorem closure_open_satisfies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) : Topology.P1 (closure A) := by
  dsimp [Topology.P1]
  have hSub : (A : Set X) ⊆ interior (closure A) :=
    interior_maximal subset_closure hA
  exact closure_mono hSub

theorem P1_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A ↔ Topology.P3 A := by
  have h₁ : Topology.P1 A → Topology.P3 A := by
    intro _hP1
    exact Topology.open_satisfies_P3 (A := A) hA
  have h₂ : Topology.P3 A → Topology.P1 A := by
    intro hP3
    have hP2 : Topology.P2 A :=
      (Topology.P3_iff_P2_of_isOpen (A := A) hA).1 hP3
    exact Topology.P2_implies_P1 (A := A) hP2
  exact ⟨h₁, h₂⟩

theorem P1_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A ↔ Topology.P2 A := by
  have h₁ : Topology.P1 A ↔ Topology.P3 A :=
    Topology.P1_iff_P3_of_isOpen (A := A) hA
  have h₂ : Topology.P3 A ↔ Topology.P2 A :=
    Topology.P3_iff_P2_of_isOpen (A := A) hA
  exact h₁.trans h₂

theorem P2_implies_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) →
      interior (closure (A : Set X)) = interior (closure (interior A)) := by
  intro hP2
  -- From P2 we know the closures coincide.
  have hClosure :
      closure (interior (A : Set X)) = closure A :=
    Topology.P2_implies_closure_interior_eq_closure (A := A) hP2
  -- Apply `interior` to both sides of the equality.
  have hInterior :
      interior (closure (interior A)) = interior (closure A) :=
    congrArg interior hClosure
  -- Rearrange to the desired orientation.
  simpa using hInterior.symm

theorem P2_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → Topology.P3 A := by
  intro hP2
  -- `closure A` is closed, so we can turn `P2` into openness.
  have hOpen : IsOpen (closure (A : Set X)) :=
    ((Topology.P2_iff_open_of_closed
        (A := closure (A : Set X)) isClosed_closure).1 hP2)
  -- Use that `interior (closure A)` equals `closure A` for an open set.
  dsimp [Topology.P3]
  have hSub : (A : Set X) ⊆ closure A := subset_closure
  simpa [hOpen.interior_eq] using hSub

theorem P1_union_of_P1 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 (A : Set X)) (hB : Topology.P1 (B : Set X)) :
    Topology.P1 (A ∪ B) := by
  dsimp [Topology.P1] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hAx =>
      have hxA : x ∈ closure (interior A) := hA hAx
      have hIncl : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact hIncl hxA
  | inr hBx =>
      have hxB : x ∈ closure (interior B) := hB hBx
      have hIncl : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact hIncl hxB

theorem P3_union_of_P3 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 (A : Set X)) (hB : Topology.P3 (B : Set X)) :
    Topology.P3 (A ∪ B) := by
  dsimp [Topology.P3] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hAx =>
      have hxA : x ∈ interior (closure A) := hA hAx
      have hIncl : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have : closure (A : Set X) ⊆ closure (A ∪ B) := by
          apply closure_mono
          intro y hy
          exact Or.inl hy
        exact this
      exact hIncl hxA
  | inr hBx =>
      have hxB : x ∈ interior (closure B) := hB hBx
      have hIncl : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have : closure (B : Set X) ⊆ closure (A ∪ B) := by
          apply closure_mono
          intro y hy
          exact Or.inr hy
        exact this
      exact hIncl hxB

theorem P2_union_of_P2 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 (A : Set X)) (hB : Topology.P2 (B : Set X)) :
    Topology.P2 (A ∪ B) := by
  dsimp [Topology.P2] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hAx =>
      have hxA : x ∈ interior (closure (interior A)) := hA hAx
      have hIncl : interior (closure (interior A))
          ⊆ interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        have : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
          apply closure_mono
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact this
      exact hIncl hxA
  | inr hBx =>
      have hxB : x ∈ interior (closure (interior B)) := hB hBx
      have hIncl : interior (closure (interior B))
          ⊆ interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        have : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
          apply closure_mono
          apply interior_mono
          intro y hy
          exact Or.inr hy
        exact this
      exact hIncl hxB

theorem P2_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 (closure (A : Set X)) := by
  intro hP2
  have hP1 : Topology.P1 (A : Set X) :=
    Topology.P2_implies_P1 (A := A) hP2
  exact Topology.P1_closure_of_P1 (A := A) hP1

theorem P3_closure_iff_P2_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) ↔ Topology.P2 (closure A) := by
  -- First, show that `P3` for `closure A` implies `P2` for `closure A`.
  have h₁ : Topology.P3 (closure (A : Set X)) → Topology.P2 (closure A) := by
    intro hP3
    -- `P3` for `closure A` gives that `closure A` is open.
    have hOpen : IsOpen (closure (A : Set X)) :=
      (Topology.P3_closure_iff_open_closure (A := A)).1 hP3
    -- On an open set, `P3` is equivalent to `P2`.
    exact
      (Topology.P3_iff_P2_of_isOpen (A := closure (A : Set X)) hOpen).1 hP3
  -- Conversely, `P2` always implies `P3`.
  have h₂ : Topology.P2 (closure A) → Topology.P3 (closure (A : Set X)) := by
    intro hP2
    exact Topology.P2_implies_P3 (A := closure (A : Set X)) hP2
  exact ⟨h₁, h₂⟩

theorem interior_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ∧ Topology.P2 (interior A) ∧ Topology.P3 (interior A) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Topology.interior_satisfies_P1 (A := A)
  · exact Topology.interior_satisfies_P2 (A := A)
  · exact Topology.interior_satisfies_P3 (A := A)

theorem P1_and_open_closure_interior_implies_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (A : Set X))
    (hOpen : IsOpen (closure (interior (A : Set X)))) :
    Topology.P3 (A : Set X) := by
  dsimp [Topology.P3]
  intro x hx
  -- From `P1`, we have membership in `closure (interior A)`.
  have hx_cl : x ∈ closure (interior A) := hP1 hx
  -- Since this set is open, its interior equals itself.
  have hEq : interior (closure (interior A)) = closure (interior A) :=
    hOpen.interior_eq
  -- Reinterpret the membership using this equality.
  have hx_int : x ∈ interior (closure (interior A)) := by
    simpa [hEq] using hx_cl
  -- Monotonicity of `interior` and `closure` gives the desired inclusion.
  have hIncl : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact hIncl hx_int

theorem P1_and_open_closure_interior_implies_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (A : Set X))
    (hOpen : IsOpen (closure (interior (A : Set X)))) :
    Topology.P2 (A : Set X) := by
  dsimp [Topology.P2] at *
  intro x hx
  -- From `P1`, we obtain membership in `closure (interior A)`.
  have hx' : x ∈ closure (interior A) := hP1 hx
  -- Since this set is open, its interior equals itself.
  have hInt : interior (closure (interior A)) = closure (interior A) :=
    hOpen.interior_eq
  -- Rewriting with this equality gives the desired result.
  simpa [hInt] using hx'

theorem open_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    Topology.P1 (A : Set X) ∧ Topology.P2 A ∧ Topology.P3 A := by
  exact
    ⟨Topology.open_satisfies_P1 (A := A) hA,
      ⟨Topology.open_satisfies_P2 (A := A) hA,
        Topology.open_satisfies_P3 (A := A) hA⟩⟩

theorem P3_implies_P1_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P3 (A : Set X) → Topology.P1 A := by
  intro hP3
  -- From `P3` and closedness we obtain that `A` is open.
  have hOpen : IsOpen (A : Set X) :=
    (Topology.P3_iff_open_of_closed (A := A) hA).1 hP3
  -- On an open set, `P1` and `P3` are equivalent.
  exact (Topology.P1_iff_P3_of_isOpen (A := A) hOpen).mpr hP3

theorem closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) ⊆ closure (interior (closure A)) := by
  exact closure_mono (interior_mono (subset_closure : (A : Set X) ⊆ closure A))

theorem P1_implies_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) →
      interior (closure (A : Set X)) = interior (closure (interior A)) := by
  intro hP1
  -- From `P1`, obtain the equality of closures.
  have hClosure :
      closure (interior (A : Set X)) = closure A :=
    (Topology.P1_iff_closure_interior_eq_closure (A := A)).1 hP1
  -- Apply `interior` to both sides.
  have hInterior :
      interior (closure (interior A)) = interior (closure A) :=
    congrArg interior hClosure
  -- Rearrange to match the desired orientation.
  simpa using hInterior.symm

theorem P2_iff_P1_of_open_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (interior (A : Set X)))) :
    Topology.P2 (A : Set X) ↔ Topology.P1 A := by
  constructor
  · intro hP2
    exact Topology.P2_implies_P1 (A := A) hP2
  · intro hP1
    dsimp [Topology.P2] at *
    simpa [hOpen.interior_eq] using hP1

theorem dense_closure_satisfies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (A : Set X) = Set.univ) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  have hInt : interior (closure (A : Set X)) = (Set.univ : Set X) := by
    simpa [hDense] using (interior_univ : interior (Set.univ : Set X) = _)
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hInt] using this

theorem P2_closure_iff_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) ↔ IsOpen (closure A) := by
  simpa using
    ((Topology.P3_closure_iff_P2_closure (A := A)).symm.trans
      (Topology.P3_closure_iff_open_closure (A := A)))

theorem empty_satisfies_all_Ps {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ∧ Topology.P2 (∅ : Set X) ∧ Topology.P3 (∅ : Set X) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [Topology.P1]
    exact Set.empty_subset _
  · dsimp [Topology.P2]
    exact Set.empty_subset _
  · dsimp [Topology.P3]
    exact Set.empty_subset _

theorem P2_implies_P1_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P2 (A : Set X) → Topology.P1 A := by
  intro hP2
  have hP3 : Topology.P3 (A : Set X) :=
    Topology.P2_implies_P3 (A := A) hP2
  exact (Topology.P3_implies_P1_of_closed (A := A) hA) hP3

theorem dense_interior_satisfies_P1_and_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior (A : Set X)) = Set.univ) :
    Topology.P1 A ∧ Topology.P2 A := by
  -- First, note that the interior of the universal set is itself.
  have hInt : interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
    simpa [hDense] using (interior_univ : interior (Set.univ : Set X) = _)
  constructor
  · -- Establish `P1`.
    dsimp [Topology.P1]
    intro x hx
    have : x ∈ (Set.univ : Set X) := by
      simp
    simpa [hDense] using this
  · -- Establish `P2`.
    dsimp [Topology.P2]
    intro x hx
    have : x ∈ (Set.univ : Set X) := by
      simp
    simpa [hInt] using this

theorem interior_closure_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (A : Set X)))
      ∧ Topology.P2 (interior (closure A))
      ∧ Topology.P3 (interior (closure A)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Topology.interior_closure_satisfies_P1 (A := A)
  · exact Topology.interior_closure_satisfies_P2 (A := A)
  · exact Topology.interior_closure_satisfies_P3 (A := A)

theorem interior_closure_closure_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (closure (A : Set X))) = interior (closure A) := by
  simpa [closure_closure]

theorem P2_implies_P2_of_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P2 (interior A) := by
  intro hP2
  dsimp [Topology.P2] at hP2 ⊢
  intro x hx
  -- Since `x ∈ interior A`, it is also in `A`.
  have hA : x ∈ (A : Set X) :=
    (interior_subset : interior A ⊆ A) hx
  -- Apply `P2` for `A` to obtain the desired membership.
  have h := hP2 hA
  -- Re-express the goal using `interior_interior`.
  simpa [interior_interior] using h

theorem P1_closure_union_of_P1
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 (A : Set X)) (hB : Topology.P1 (B : Set X)) :
    Topology.P1 (closure (A ∪ B : Set X)) := by
  -- First, `P1` holds for the union `A ∪ B`.
  have hUnion : Topology.P1 (A ∪ B : Set X) :=
    Topology.P1_union_of_P1 (A := A) (B := B) hA hB
  -- Then, apply the closure-stability of `P1`.
  exact Topology.P1_closure_of_P1 (A := A ∪ B) hUnion

theorem P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → (Topology.P1 A ∧ Topology.P3 A) := by
  intro hP2
  exact
    ⟨Topology.P2_implies_P1 (A := A) hP2,
      Topology.P2_implies_P3 (A := A) hP2⟩

theorem interior_closure_interior_satisfies_P2
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (closure (interior A))) := by
  simpa using
    (Topology.interior_closure_satisfies_P2 (A := interior A))

theorem univ_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ∧ Topology.P2 (Set.univ : Set X) ∧ Topology.P3 (Set.univ : Set X) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [Topology.P1]
    simpa [interior_univ, closure_univ]
      using (subset_rfl : (Set.univ : Set X) ⊆ Set.univ)
  · dsimp [Topology.P2]
    simpa [interior_univ, closure_univ]
      using (subset_rfl : (Set.univ : Set X) ⊆ Set.univ)
  · dsimp [Topology.P3]
    simpa [interior_univ, closure_univ]
      using (subset_rfl : (Set.univ : Set X) ⊆ Set.univ)

theorem closure_interior_closure_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (closure (A : Set X))))
      = closure (interior (closure A)) := by
  simpa [closure_closure]

theorem P1_and_P2_iff_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    (Topology.P1 (A : Set X) ∧ Topology.P2 A) ↔ Topology.P2 A := by
  constructor
  · intro h
    exact h.2
  · intro hP2
    exact ⟨Topology.P2_implies_P1 (A := A) hP2, hP2⟩

theorem P3_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P3 A := by
  intro hP3cl
  dsimp [Topology.P3] at hP3cl ⊢
  intro x hx
  -- `x` belongs to the closure of `A`.
  have hx_closure : x ∈ closure (A : Set X) := subset_closure hx
  -- Use `P3` for `closure A` to obtain the desired inclusion.
  have hIncl : closure (A : Set X) ⊆ interior (closure A) := by
    simpa [closure_closure] using hP3cl
  exact hIncl hx_closure

theorem P1_iff_P3_of_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (A : Set X)) ↔ Topology.P3 (interior A) := by
  have hOpen : IsOpen (interior (A : Set X)) := isOpen_interior
  simpa using (Topology.P1_iff_P3_of_isOpen (A := interior A) hOpen)

theorem interior_closure_interior_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (interior A)))
      ∧ Topology.P2 (interior (closure (interior A)))
      ∧ Topology.P3 (interior (closure (interior A))) := by
  exact
    ⟨Topology.interior_closure_interior_satisfies_P1 (A := A),
      Topology.interior_closure_interior_satisfies_P2 (A := A),
      Topology.interior_closure_interior_satisfies_P3 (A := A)⟩

theorem P1_iff_P2_and_P3_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    Topology.P1 (A : Set X) ↔ (Topology.P2 A ∧ Topology.P3 A) := by
  constructor
  · intro hP1
    have hP2 : Topology.P2 (A : Set X) :=
      (Topology.P1_iff_P2_of_isOpen (A := A) hA).1 hP1
    have hP3 : Topology.P3 (A : Set X) :=
      (Topology.P1_iff_P3_of_isOpen (A := A) hA).1 hP1
    exact And.intro hP2 hP3
  · rintro ⟨hP2, _hP3⟩
    exact (Topology.P1_iff_P2_of_isOpen (A := A) hA).2 hP2

theorem P1_iUnion_of_P1 {X : Type*} [TopologicalSpace X] {ι : Sort*}
    {S : ι → Set X} (hS : ∀ i, Topology.P1 (S i)) :
    Topology.P1 (⋃ i, S i) := by
  dsimp [Topology.P1] at hS ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hx_cl : x ∈ closure (interior (S i)) := (hS i) hx_i
  have hIncl : closure (interior (S i)) ⊆ closure (interior (⋃ i, S i)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  exact hIncl hx_cl

theorem P2_iUnion_of_P2
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {S : ι → Set X}
    (hS : ∀ i, Topology.P2 (S i)) :
    Topology.P2 (⋃ i, S i) := by
  dsimp [Topology.P2] at hS ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- Use `P2` for the chosen set `S i`.
  have hx_int : x ∈ interior (closure (interior (S i))) := (hS i) hx_i
  -- Show this interior is contained in the desired interior.
  have hIncl :
      interior (closure (interior (S i)))
        ⊆ interior (closure (interior (⋃ i, S i))) := by
    apply interior_mono
    have : closure (interior (S i))
        ⊆ closure (interior (⋃ i, S i)) := by
      apply closure_mono
      apply interior_mono
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact this
  exact hIncl hx_int

theorem open_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → IsOpen (closure (A : Set X)) := by
  intro hP3
  exact (Topology.P3_closure_iff_open_closure (A := A)).1 hP3

theorem P3_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A : Set X) → Topology.P1 (closure (A : Set X)) := by
  intro hP3
  dsimp [Topology.P3] at hP3
  dsimp [Topology.P1]
  exact closure_mono hP3

theorem P3_iUnion_of_P3
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {S : ι → Set X}
    (hS : ∀ i, Topology.P3 (S i)) :
    Topology.P3 (⋃ i, S i) := by
  dsimp [Topology.P3] at hS ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- Use `P3` for the chosen set `S i`.
  have hx_int : x ∈ interior (closure (S i)) := (hS i) hx_i
  -- Show this interior is contained in the desired interior.
  have hIncl :
      interior (closure (S i)) ⊆ interior (closure (⋃ i, S i)) := by
    apply interior_mono
    have : closure (S i) ⊆ closure (⋃ i, S i) := by
      apply closure_mono
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact this
  exact hIncl hx_int

theorem interior_closure_univ_implies_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure (A : Set X)) = (Set.univ : Set X)) :
    Topology.P3 (A : Set X) := by
  dsimp [Topology.P3]
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h] using this

theorem P1_iff_P2_of_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (A : Set X)) ↔ Topology.P2 (interior A) := by
  have h₁ := (Topology.P1_iff_P3_of_interior (A := A))
  have h₂ := (Topology.P3_iff_P2_of_interior (A := A))
  exact h₁.trans h₂

theorem P2_implies_P1_v2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 A := by
  intro hP2
  dsimp [Topology.P2] at hP2
  dsimp [Topology.P1]
  have hIntSub : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset (s := closure (interior A))
  exact hP2.trans hIntSub

theorem P2_of_open_closure_interior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hEq : closure (interior (A : Set X)) = closure A)
    (hOpen : IsOpen (closure (interior A))) :
    Topology.P2 (A : Set X) := by
  -- From the equality of closures, deduce `P1` for `A`.
  have hP1 : Topology.P1 (A : Set X) :=
    ((Topology.P1_iff_closure_interior_eq_closure (A := A)).2 hEq)
  -- Combine `P1` with the openness assumption to obtain `P2`.
  exact
    Topology.P1_and_open_closure_interior_implies_P2
      (A := A) hP1 hOpen

theorem P3_implies_P2_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P3 (A : Set X) → Topology.P2 A := by
  intro hP3
  exact (Topology.P3_iff_P2_of_closed (A := A) hA).1 hP3

theorem open_closure_implies_P2_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    Topology.P2 (closure (A : Set X)) := by
  simpa using
    (Topology.open_satisfies_P2 (A := closure (A : Set X)) hOpen)

theorem open_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → IsOpen (closure (A : Set X)) := by
  intro hP2
  exact (Topology.P2_closure_iff_open_closure (A := A)).1 hP2

theorem P1_and_P3_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) → Topology.P3 A → Topology.P2 A := by
  intro hP1 hP3
  -- From `P1`, obtain the equality of closures.
  have hClosure :
      closure (interior (A : Set X)) = closure A :=
    (Topology.P1_iff_closure_interior_eq_closure (A := A)).1 hP1
  -- Unfold the goal.
  dsimp [Topology.P2]
  intro x hxA
  -- Use `P3` to place `x` inside `interior (closure A)`.
  have hxInt : x ∈ interior (closure A) := hP3 hxA
  -- Reinterpret this membership via the equality of interiors.
  have hIntEq :
      interior (closure (interior A)) = interior (closure A) :=
    congrArg interior hClosure
  simpa [hIntEq] using hxInt

theorem open_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → IsOpen (closure A) → IsOpen (closure (interior A)) := by
  intro hP2 hOpen
  have hEq : closure (interior (A : Set X)) = closure A :=
    Topology.P2_implies_closure_interior_eq_closure (A := A) hP2
  simpa [hEq] using hOpen

theorem P2_iff_P1_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  constructor
  · intro hP2
    exact And.intro
      (Topology.P2_implies_P1 (A := A) hP2)
      (Topology.P2_implies_P3 (A := A) hP2)
  · rintro ⟨hP1, hP3⟩
    exact Topology.P1_and_P3_implies_P2 (A := A) hP1 hP3

theorem interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (A : Set X)))) = interior (closure A) := by
  -- We prove the equality by showing mutual inclusion.
  apply Set.Subset.antisymm
  · -- First, `⊆`.
    have h :
        interior (closure (interior (closure (A : Set X))))
          ⊆ interior (closure (closure (A : Set X))) :=
      interior_closure_interior_subset_closure (A := closure (A : Set X))
    simpa [closure_closure] using h
  · -- Second, `⊇`.
    -- `interior (closure A)` is open and contained in `closure (interior (closure A))`.
    have hSub :
        interior (closure (A : Set X))
          ⊆ closure (interior (closure (A : Set X))) :=
      subset_closure
    have hIncl :
        interior (closure (A : Set X))
          ⊆ interior (closure (interior (closure A))) :=
      interior_maximal hSub isOpen_interior
    simpa using hIncl

theorem P1_closure_iUnion_of_P1
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {S : ι → Set X}
    (hS : ∀ i, Topology.P1 (S i)) :
    Topology.P1 (closure (⋃ i, S i : Set X)) := by
  -- First, `P1` holds for the union `⋃ i, S i`.
  have hUnion : Topology.P1 (⋃ i, S i : Set X) :=
    Topology.P1_iUnion_of_P1 (S := S) hS
  -- Then, apply the closure-stability of `P1`.
  exact Topology.P1_closure_of_P1 (A := ⋃ i, S i) hUnion

theorem nonempty_interior_of_nonempty_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (A : Set X)) (hNon : (A : Set X).Nonempty) :
    (interior (A : Set X)).Nonempty := by
  classical
  by_contra hInt
  -- From `¬ (interior A).Nonempty`, deduce `interior A = ∅`.
  have hIntEmpty : interior (A : Set X) = (∅ : Set X) :=
    (Set.not_nonempty_iff_eq_empty).1 hInt
  -- Hence its closure is also empty.
  have hClosureEmpty : closure (interior (A : Set X)) = (∅ : Set X) := by
    simpa [hIntEmpty, closure_empty] using rfl
  -- Pick an element of `A` (it exists by `hNon`).
  rcases hNon with ⟨x, hxA⟩
  -- `P1` puts this element inside the (empty) closure, contradiction.
  have : x ∈ closure (interior (A : Set X)) := hP1 hxA
  simpa [hClosureEmpty] using this

theorem closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (A : Set X))))) =
      closure (interior (closure A)) := by
  -- Use the previously established equality for the inner term.
  have h :
      interior (closure (interior (closure (A : Set X)))) =
        interior (closure A) :=
    interior_closure_interior_closure_eq (A := A)
  -- Apply `closure` to both sides.
  simpa using congrArg closure h

theorem P1_closure_iff_P1_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P1 (closure (A : Set X)) ↔ Topology.P1 A := by
  have hEq : closure (A : Set X) = A := hA.closure_eq
  simpa [hEq] using
    (Iff.rfl : Topology.P1 (closure (A : Set X)) ↔ Topology.P1 (closure (A : Set X)))

theorem P3_and_closure_interior_eq_closure_implies_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A : Set X) →
      closure (interior A) = closure A → Topology.P2 A := by
  intro hP3 hEq
  -- Derive `P1` from the equality of closures.
  have hP1 : Topology.P1 (A : Set X) :=
    (Topology.P1_iff_closure_interior_eq_closure (A := A)).2 hEq
  -- Combine `P1` and `P3` to obtain `P2`.
  exact Topology.P1_and_P3_implies_P2 (A := A) hP1 hP3

theorem P2_closure_iff_P2_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P2 (closure (A : Set X)) ↔ Topology.P2 A := by
  have hEq : closure (A : Set X) = A := hA.closure_eq
  simpa [hEq] using
    (Iff.rfl :
      Topology.P2 (closure (A : Set X)) ↔ Topology.P2 (closure (A : Set X)))

theorem nonempty_interior_of_nonempty_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → A.Nonempty → (interior (A : Set X)).Nonempty := by
  intro hP2 hNon
  -- Derive `P1` from `P2`.
  have hP1 : Topology.P1 (A : Set X) :=
    Topology.P2_implies_P1 (A := A) hP2
  -- Apply the existing lemma for `P1`.
  exact nonempty_interior_of_nonempty_P1 (A := A) hP1 hNon

theorem interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (A : Set X)))))) =
      interior (closure A) := by
  calc
    interior (closure (interior (closure (interior (closure (A : Set X)))))) =
        interior (closure (interior (closure (A : Set X)))) := by
          simpa using
            (interior_closure_interior_closure_eq
              (A := interior (closure (A : Set X))))
    _ = interior (closure (A : Set X)) := by
          simpa using
            (interior_closure_interior_closure_eq (A := A))

theorem nonempty_interior_closure_of_nonempty_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A : Set X) → A.Nonempty →
      (interior (closure (A : Set X))).Nonempty := by
  intro hP3 hNon
  rcases hNon with ⟨x, hxA⟩
  have hxInt : x ∈ interior (closure (A : Set X)) := hP3 hxA
  exact ⟨x, hxInt⟩

theorem interior_closure_inter_subset_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A ∩ B) : Set X))
      ⊆ interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- Show `x ∈ interior (closure A)`.
  have hA : x ∈ interior (closure A) := by
    -- `(A ∩ B) ⊆ A`
    have hSub : (A ∩ B : Set X) ⊆ A := by
      intro y hy
      exact hy.1
    -- `closure (A ∩ B) ⊆ closure A`
    have hClSub : closure (A ∩ B : Set X) ⊆ closure A :=
      closure_mono hSub
    -- Now use monotonicity of `interior`.
    exact (interior_mono hClSub) hx
  -- Show `x ∈ interior (closure B)`.
  have hB : x ∈ interior (closure B) := by
    -- `(A ∩ B) ⊆ B`
    have hSub : (A ∩ B : Set X) ⊆ B := by
      intro y hy
      exact hy.2
    -- `closure (A ∩ B) ⊆ closure B`
    have hClSub : closure (A ∩ B : Set X) ⊆ closure B :=
      closure_mono hSub
    -- Apply monotonicity of `interior`.
    exact (interior_mono hClSub) hx
  exact And.intro hA hB

theorem interior_closure_eq_self_of_P3_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (A : Set X)) :
    interior (closure (A : Set X)) = A := by
  -- First, `interior (closure A) ⊆ A` because `A` is closed.
  have h₁ : interior (closure (A : Set X)) ⊆ A := by
    have h : interior (closure (A : Set X)) ⊆ closure (A : Set X) :=
      interior_subset
    simpa [hA_closed.closure_eq] using h
  -- Second, `A ⊆ interior (closure A)` by `P3`.
  have h₂ : (A : Set X) ⊆ interior (closure A) := by
    dsimp [Topology.P3] at hP3
    exact hP3
  exact subset_antisymm h₁ h₂

theorem P1_closure_iff_closure_interior_closure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (A : Set X)) ↔
      closure (interior (closure A)) = closure A := by
  simpa [closure_closure] using
    (Topology.P1_iff_closure_interior_eq_closure
      (A := closure (A : Set X)))

theorem union_interior_closure_subset_interior_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A : Set X)) ∪ interior (closure B) ⊆
      interior (closure (A ∪ B : Set X)) := by
  intro x hx
  cases hx with
  | inl hAx =>
      -- `x` lies in `interior (closure A)`
      -- Show that this interior is contained in the desired interior.
      have hIncl : closure (A : Set X) ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inl hy
      have hIntIncl :
          interior (closure (A : Set X))
            ⊆ interior (closure (A ∪ B)) :=
        interior_mono hIncl
      exact hIntIncl hAx
  | inr hBx =>
      -- Analogous argument for the `B` component.
      have hIncl : closure (B : Set X) ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inr hy
      have hIntIncl :
          interior (closure (B : Set X))
            ⊆ interior (closure (A ∪ B)) :=
        interior_mono hIncl
      exact hIntIncl hBx

theorem P1_iff_P2_and_P3_of_open_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (interior (A : Set X)))) :
    Topology.P1 (A : Set X) ↔ (Topology.P2 A ∧ Topology.P3 A) := by
  constructor
  · intro hP1
    have hP2 : Topology.P2 (A : Set X) :=
      Topology.P1_and_open_closure_interior_implies_P2 (A := A) hP1 hOpen
    have hP3 : Topology.P3 (A : Set X) :=
      Topology.P1_and_open_closure_interior_implies_P3 (A := A) hP1 hOpen
    exact And.intro hP2 hP3
  · rintro ⟨hP2, _hP3⟩
    exact Topology.P2_implies_P1 (A := A) hP2

theorem P2_iff_P3_and_closure_interior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) ↔
      (Topology.P3 A ∧ closure (interior A) = closure A) := by
  constructor
  · intro hP2
    exact And.intro
      (Topology.P2_implies_P3 (A := A) hP2)
      (Topology.P2_implies_closure_interior_eq_closure (A := A) hP2)
  · rintro ⟨hP3, hEq⟩
    exact
      Topology.P3_and_closure_interior_eq_closure_implies_P2
        (A := A) hP3 hEq

theorem interior_closure_interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior (closure (A : Set X))))))))
      = interior (closure A) := by
  calc
    interior (closure (interior (closure (interior (closure (interior (closure (A : Set X)))))))) =
        interior (closure (interior (closure (interior (closure (A : Set X)))))) := by
          simpa using
            (interior_closure_interior_closure_eq
              (A := interior (closure (interior (closure (A : Set X))))))
    _ = interior (closure (interior (closure (A : Set X)))) := by
          simpa using
            (interior_closure_interior_closure_eq
              (A := interior (closure (A : Set X))))
    _ = interior (closure (A : Set X)) := by
          simpa using
            (interior_closure_interior_closure_eq (A := A))

theorem open_closure_implies_P1_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    Topology.P1 (closure (A : Set X)) := by
  simpa using
    (Topology.open_satisfies_P1 (A := closure (A : Set X)) hOpen)

theorem interior_eq_self_of_P2_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P2 (A : Set X) → interior A = A := by
  intro hP2
  have hOpen : IsOpen (A : Set X) :=
    (Topology.P2_iff_open_of_closed (A := A) hA).1 hP2
  simpa using hOpen.interior_eq

theorem P1_and_interior_empty_implies_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) → interior (A : Set X) = ∅ → A = ∅ := by
  intro hP1 hIntEmpty
  apply Set.Subset.antisymm
  · intro x hxA
    have : x ∈ closure (interior (A : Set X)) := hP1 hxA
    simpa [hIntEmpty, closure_empty] using this
  · simpa using (Set.empty_subset (A := A))

theorem P3_iff_exists_open_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A : Set X) ↔
      ∃ U : Set X, IsOpen U ∧ (A : Set X) ⊆ U ∧ U ⊆ closure (A : Set X) := by
  classical
  constructor
  · intro hP3
    refine ⟨interior (closure (A : Set X)), isOpen_interior, ?_, ?_⟩
    · simpa using hP3
    · exact interior_subset
  · rintro ⟨U, hOpenU, hASubU, hUSub⟩
    dsimp [Topology.P3]
    have hU_into :
        U ⊆ interior (closure (A : Set X)) :=
      interior_maximal hUSub hOpenU
    exact hASubU.trans hU_into

theorem P2_and_interior_empty_implies_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → interior (A : Set X) = ∅ → A = ∅ := by
  intro hP2 hIntEmpty
  -- Derive `P1` from `P2`.
  have hP1 : Topology.P1 (A : Set X) :=
    Topology.P2_implies_P1 (A := A) hP2
  -- Apply the existing lemma for `P1`.
  exact
    Topology.P1_and_interior_empty_implies_empty
      (A := A) hP1 hIntEmpty

theorem interior_closure_interior_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    interior (closure (interior (A : Set X))) ⊆
      interior (closure (interior B)) := by
  -- Lift the inclusion `A ⊆ B` through `interior` and `closure`.
  have h : closure (interior (A : Set X)) ⊆ closure (interior B) := by
    apply closure_mono
    apply interior_mono
    exact hAB
  -- Apply monotonicity of `interior`.
  exact interior_mono h

theorem open_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    Topology.P3 (A : Set X) → IsOpen A := by
  intro hP3
  exact (Topology.P3_iff_open_of_closed (A := A) hClosed).1 hP3

theorem P2_iff_exists_open_subset_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) ↔
      ∃ U : Set X, IsOpen U ∧ (A : Set X) ⊆ U ∧
        U ⊆ interior (closure (interior A)) := by
  classical
  constructor
  · intro hP2
    refine
      ⟨interior (closure (interior (A : Set X))),
        isOpen_interior, ?_, ?_⟩
    · exact hP2
    · exact subset_rfl
  · rintro ⟨U, _hOpenU, hASubU, hUSub⟩
    dsimp [Topology.P2] at *
    exact hASubU.trans hUSub

theorem open_of_P2_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    Topology.P2 (A : Set X) → IsOpen A := by
  intro hP2
  exact (Topology.P2_iff_open_of_closed (A := A) hClosed).1 hP2

theorem interior_closure_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A \ B) : Set X)) ⊆ interior (closure A) := by
  -- `A \ B` is contained in `A`.
  have hSub : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Therefore, the closure of `A \ B` is contained in the closure of `A`.
  have hClSub : closure ((A \ B) : Set X) ⊆ closure A :=
    closure_mono hSub
  -- Apply monotonicity of `interior` to obtain the desired inclusion.
  exact interior_mono hClSub

theorem interior_closure_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    interior (closure (A : Set X)) ⊆ interior (closure B) := by
  exact interior_mono (closure_mono hAB)

theorem closure_interior_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    closure (interior (A : Set X)) ⊆ closure (interior B) := by
  exact closure_mono (interior_mono hAB)

theorem interior_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ interior (closure A) := by
  exact interior_mono (subset_closure : (A : Set X) ⊆ closure A)

theorem interior_eq_self_of_P3_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P3 (A : Set X) → interior (A : Set X) = A := by
  intro hP3
  -- A closed set satisfying `P3` is also open.
  have hOpen : IsOpen (A : Set X) :=
    (Topology.open_of_P3_closed (A := A) hA) hP3
  -- For an open set, its interior is the set itself.
  simpa using hOpen.interior_eq

theorem closure_interior_union_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X)) ∪ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hAx =>
      have hIncl :
          closure (interior (A : Set X))
            ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact hIncl hAx
  | inr hBx =>
      have hIncl :
          closure (interior (B : Set X))
            ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact hIncl hBx

theorem P2_closure_interior_iff_open_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (A : Set X))) ↔ IsOpen (closure (interior A)) := by
  have hClosed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  simpa using
    (Topology.P2_iff_open_of_closed
      (A := closure (interior (A : Set X))) hClosed)

theorem interior_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior ((A ∩ B) : Set X) ⊆ interior A ∩ interior B := by
  intro x hx
  -- First, show `x ∈ interior A`.
  have hA : x ∈ interior A := by
    -- Since `A ∩ B ⊆ A`, monotonicity of `interior` gives the inclusion.
    have hSub : (A ∩ B : Set X) ⊆ A := by
      intro y hy
      exact hy.1
    exact (interior_mono hSub) hx
  -- Next, show `x ∈ interior B`.
  have hB : x ∈ interior B := by
    -- Similarly, `A ∩ B ⊆ B`.
    have hSub : (A ∩ B : Set X) ⊆ B := by
      intro y hy
      exact hy.2
    exact (interior_mono hSub) hx
  -- Combine the two inclusions.
  exact And.intro hA hB

theorem interior_closure_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (A : Set X) = (Set.univ : Set X)) :
    interior (closure (A : Set X)) = (Set.univ : Set X) := by
  simpa [hDense] using
    (interior_univ : interior (Set.univ : Set X) = Set.univ)

theorem closure_interior_inter_subset_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior ((A ∩ B) : Set X))
      ⊆ closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- Inclusion into `closure (interior A)`
  have hA :
      closure (interior ((A ∩ B) : Set X)) ⊆ closure (interior A) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact hy.1
  -- Inclusion into `closure (interior B)`
  have hB :
      closure (interior ((A ∩ B) : Set X)) ⊆ closure (interior B) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact hy.2
  exact And.intro (hA hx) (hB hx)

theorem closure_interior_closure_satisfies_P1
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior (closure (A : Set X)))) := by
  -- `P1` holds for `interior (closure A)` by a previously established lemma.
  have hP1 : Topology.P1 (interior (closure (A : Set X))) :=
    Topology.interior_closure_satisfies_P1 (A := A)
  -- `P1` is stable under taking closures.
  exact
    Topology.P1_closure_of_P1
      (A := interior (closure (A : Set X))) hP1

theorem nonempty_interior_closure_interior_of_nonempty_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → A.Nonempty →
      (interior (closure (interior (A : Set X)))).Nonempty := by
  intro hP2 hNon
  rcases hNon with ⟨x, hxA⟩
  have hxInt : x ∈ interior (closure (interior (A : Set X))) := hP2 hxA
  exact ⟨x, hxInt⟩

theorem P1_iff_exists_open_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) ↔
      ∃ U : Set X, IsOpen U ∧ U ⊆ A ∧ A ⊆ closure U := by
  classical
  constructor
  · intro hP1
    refine ⟨interior (A : Set X), isOpen_interior, interior_subset, ?_⟩
    simpa using hP1
  · rintro ⟨U, hOpenU, hUSubA, hASubClosU⟩
    dsimp [Topology.P1]
    intro x hxA
    have hUSubInt : (U : Set X) ⊆ interior A :=
      interior_maximal hUSubA hOpenU
    have hxClosU : x ∈ closure U := hASubClosU hxA
    have hClosIncl : closure U ⊆ closure (interior A) :=
      closure_mono hUSubInt
    exact hClosIncl hxClosU

theorem closure_interior_eq_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    closure (interior (A : Set X)) = closure A := by
  simpa [hA.interior_eq]

theorem closure_interior_union_satisfies_P1
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (closure (interior (A : Set X)) ∪ closure (interior B)) := by
  -- Each of the two sets `closure (interior A)` and `closure (interior B)` satisfies `P1`.
  have hA : Topology.P1 (closure (interior (A : Set X))) :=
    Topology.closure_interior_satisfies_P1 (A := A)
  have hB : Topology.P1 (closure (interior (B : Set X))) :=
    Topology.closure_interior_satisfies_P1 (A := B)
  -- `P1` is stable under finite unions, so their union also satisfies `P1`.
  exact
    Topology.P1_union_of_P1
      (A := closure (interior (A : Set X)))
      (B := closure (interior B))
      hA hB

theorem nonempty_interior_closure_of_nonempty_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) → A.Nonempty →
      (interior (closure (A : Set X))).Nonempty := by
  intro hP1 hNon
  -- Obtain a point in `interior A` using the existing lemma.
  have hIntNon : (interior (A : Set X)).Nonempty :=
    nonempty_interior_of_nonempty_P1 (A := A) hP1 hNon
  rcases hIntNon with ⟨x, hxIntA⟩
  -- `interior A` is contained in `interior (closure A)`.
  have hxIntCl : x ∈ interior (closure (A : Set X)) :=
    (interior_subset_interior_closure (A := A)) hxIntA
  exact ⟨x, hxIntCl⟩

theorem P2_of_interior_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior (A : Set X) = A) : Topology.P2 (A : Set X) := by
  -- `interior A` is open, so `A` is open by the given equality.
  have hOpen : IsOpen (A : Set X) := by
    simpa [hInt] using (isOpen_interior : IsOpen (interior (A : Set X)))
  -- Open sets satisfy `P2`.
  exact Topology.open_satisfies_P2 (A := A) hOpen

theorem closure_interior_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior ((A \ B) : Set X))
      ⊆ closure (interior A) := by
  -- First, note that `A \ B ⊆ A`.
  have hSub : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Monotonicity of `interior` lifts this inclusion.
  have hIntSub : interior ((A \ B) : Set X) ⊆ interior A :=
    interior_mono hSub
  -- Applying `closure` preserves the inclusion.
  exact closure_mono hIntSub

theorem closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (A : Set X)))) =
      closure (interior A) := by
  apply Set.Subset.antisymm
  · -- `⊆` direction
    have h₁ :
        interior (closure (interior (A : Set X))) ⊆
          closure (interior A) := by
      -- `interior s ⊆ s` with `s = closure (interior A)`
      simpa using (interior_subset :
        interior (closure (interior (A : Set X))) ⊆
          closure (interior (A : Set X)))
    simpa [closure_closure] using (closure_mono h₁)
  · -- `⊇` direction
    have h₂ : interior A ⊆ interior (closure (interior A)) := by
      have hSub : (interior A : Set X) ⊆ closure (interior A) :=
        subset_closure
      have h := interior_mono hSub
      simpa [interior_interior] using h
    simpa using (closure_mono h₂)

theorem closure_interior_closure_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    closure (interior (closure (A : Set X))) ⊆
      closure (interior (closure B)) := by
  -- First, extend the inclusion through `closure`.
  have h₁ : closure (A : Set X) ⊆ closure B := closure_mono hAB
  -- Next, push it through `interior`.
  have h₂ : interior (closure (A : Set X)) ⊆ interior (closure B) :=
    interior_mono h₁
  -- Finally, apply `closure` once more.
  exact closure_mono h₂

theorem open_of_subset_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    (A : Set X) ⊆ interior A → IsOpen A := by
  intro hA
  have h₁ : interior (A : Set X) ⊆ A := interior_subset
  have hEq : interior (A : Set X) = A := subset_antisymm h₁ hA
  simpa [hEq] using (isOpen_interior : IsOpen (interior (A : Set X)))

theorem closure_interior_union_eq_closure_union_of_open
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    closure (interior (A ∪ B : Set X)) = closure (A ∪ B) := by
  have hInt : interior (A ∪ B : Set X) = A ∪ B :=
    (hA.union hB).interior_eq
  simpa [hInt]

theorem interior_closure_union_eq
    {X : Type*} [TopologicalSpace X] (A B : Set X) :
    interior (closure ((A ∪ B) : Set X)) =
      interior (closure (A : Set X) ∪ closure B) := by
  simpa [closure_union]

theorem open_closure_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    Topology.P1 (closure (A : Set X))
      ∧ Topology.P2 (closure A)
      ∧ Topology.P3 (closure A) := by
  have hP1 : Topology.P1 (closure (A : Set X)) :=
    open_closure_implies_P1_closure (A := A) hOpen
  have hP2 : Topology.P2 (closure (A : Set X)) :=
    open_closure_implies_P2_closure (A := A) hOpen
  have hP3 : Topology.P3 (closure (A : Set X)) :=
    Topology.open_satisfies_P3 (A := closure (A : Set X)) hOpen
  exact And.intro hP1 (And.intro hP2 hP3)

theorem subset_interior_closure_interior_implies_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (A ⊆ interior (closure (interior A))) → Topology.P1 A := by
  intro hA
  dsimp [Topology.P1] at *
  intro x hx
  have hx_int : x ∈ interior (closure (interior A)) := hA hx
  have hx_cl : x ∈ closure (interior A) :=
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx_int
  exact hx_cl

theorem closure_closure_interior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (closure (interior (A : Set X))) = closure (interior A) := by
  simpa [closure_closure]

theorem subset_interior_closure_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A : Set X) → (A : Set X) ⊆ interior (closure A) := by
  intro hP3
  dsimp [Topology.P3] at hP3
  exact hP3

theorem closure_interior_interior_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (interior (A : Set X))) = closure (interior A) := by
  simpa [interior_interior]

theorem P3_of_interior_closure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) = closure A → Topology.P3 A := by
  intro hEq
  -- From the equality, `closure A` coincides with its interior and hence is open.
  have hOpen : IsOpen (closure (A : Set X)) := by
    have hOpenInt : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    simpa [hEq] using hOpenInt
  -- An open closure implies `P3` for the original set.
  exact Topology.closure_open_satisfies_P3 (A := A) hOpen

theorem clopen_of_closed_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP3 : Topology.P3 (A : Set X)) :
    IsOpen A ∧ IsClosed (A : Set X) := by
  have hOpen : IsOpen (A : Set X) :=
    (Topology.open_of_P3_closed (A := A) hClosed) hP3
  exact And.intro hOpen hClosed

theorem dense_interior_satisfies_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P3 (A : Set X) := by
  dsimp [Topology.P3]
  intro x hxA
  -- First, deduce that `closure A = univ`.
  have hClosure_eq : closure (A : Set X) = (Set.univ : Set X) := by
    -- `closure (interior A) ⊆ closure A`
    have hSub : closure (interior (A : Set X)) ⊆ closure A :=
      closure_mono (interior_subset : interior (A : Set X) ⊆ A)
    -- Rewrite the left-hand side using `hDense`.
    have : (Set.univ : Set X) ⊆ closure A := by
      simpa [hDense] using hSub
    -- Combine the inclusions to obtain equality.
    exact Set.Subset.antisymm (Set.subset_univ _) this
  -- Therefore, the interior of `closure A` is the entire space.
  have hInt_eq : interior (closure (A : Set X)) = (Set.univ : Set X) := by
    simpa [hClosure_eq] using
      (interior_univ : interior (Set.univ : Set X) = Set.univ)
  -- Conclude the required membership.
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hInt_eq] using this

theorem P2_implies_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P2 (A : Set X) → Topology.P3 A := by
  intro hP2
  exact (Topology.P3_iff_P2_of_closed (A := A) hA).2 hP2

theorem P3_closure_iff_P3_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P3 (closure (A : Set X)) ↔ Topology.P3 A := by
  have hEq : closure (A : Set X) = A := hA.closure_eq
  simpa [hEq] using
    (Iff.rfl :
      Topology.P3 (closure (A : Set X)) ↔ Topology.P3 (closure (A : Set X)))

theorem P2_iff_interior_eq_self_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P2 (A : Set X) ↔ interior A = A := by
  constructor
  · intro hP2
    exact (interior_eq_self_of_P2_closed (A := A) hA) hP2
  · intro hIntEq
    exact P2_of_interior_eq_self (A := A) hIntEq

theorem subset_interior_closure_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    ((A : Set X) ⊆ interior (closure A)) ↔ Topology.P3 (A : Set X) := by
  rfl

theorem interior_closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (A : Set X))))) =
      interior (closure (interior A)) := by
  simpa using
    (interior_closure_interior_closure_eq (A := interior (A : Set X)))

theorem interior_closure_subset_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    interior (closure (A : Set X)) ⊆ A := by
  have h : interior (closure (A : Set X)) ⊆ closure A := interior_subset
  simpa [hA.closure_eq] using h

theorem open_of_P2_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (A : Set X))) → IsOpen (closure (interior A)) := by
  intro hP2
  exact
    (Topology.P2_closure_interior_iff_open_closure_interior (A := A)).1 hP2

theorem interior_closure_eq_self_of_P3_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) →
      interior (closure (A : Set X)) = closure A := by
  intro hP3
  have hOpen : IsOpen (closure (A : Set X)) :=
    Topology.open_of_P3_closure (A := A) hP3
  simpa using hOpen.interior_eq

theorem closure_inter_subset_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((A ∩ B) : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  have hA : closure ((A ∩ B) : Set X) ⊆ closure A := by
    apply closure_mono
    intro y hy
    exact hy.1
  have hB : closure ((A ∩ B) : Set X) ⊆ closure B := by
    apply closure_mono
    intro y hy
    exact hy.2
  exact And.intro (hA hx) (hB hx)

theorem interior_interior_closure_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (interior (closure (A : Set X))) = interior (closure A) := by
  simpa [interior_interior]

theorem P2_of_P2_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (A : Set X))) → Topology.P2 (interior A) := by
  intro hP2
  dsimp [Topology.P2] at hP2 ⊢
  intro x hxIntA
  -- `x` is in the closure of `interior A`.
  have hx_cl : x ∈ closure (interior (A : Set X)) :=
    subset_closure hxIntA
  -- Apply `P2` for `closure (interior A)`.
  have hx :
      x ∈ interior (closure (interior (closure (interior (A : Set X))))) :=
    hP2 hx_cl
  -- Identify the target interior using the established equality lemma.
  have hEq :
      interior (closure (interior (closure (interior (A : Set X))))) =
        interior (closure (interior A)) := by
    simpa using
      (interior_closure_interior_closure_eq (A := interior (A : Set X)))
  -- Conclude the desired membership.
  simpa [hEq, interior_interior] using hx

theorem P3_and_interior_closure_empty_implies_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A : Set X) →
      interior (closure (A : Set X)) = ∅ → A = ∅ := by
  intro hP3 hIntEmpty
  apply Set.Subset.antisymm
  · intro x hxA
    have : x ∈ interior (closure (A : Set X)) := hP3 hxA
    simpa [hIntEmpty] using this
  · simpa using (Set.empty_subset (A := A))

theorem closure_interior_closure_interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure (interior (closure (A : Set X))))))))) =
      closure (interior (closure A)) := by
  -- Step 1: Reduce the innermost seven-layer pattern to the canonical form.
  have h₁ :
      closure
        (interior
          (closure
            (interior
              (closure (interior (closure A)))))) =
        closure (interior (closure A)) := by
    simpa using
      (closure_interior_closure_interior_closure_interior_closure_eq (A := A))
  -- Step 2: Substitute `h₁` and finish with the five-layer equality lemma.
  calc
    closure
        (interior
          (closure
            (interior
              (closure (interior (closure (interior (closure A)))))))) =
        closure (interior (closure (interior (closure A)))) := by
          simpa [h₁]
    _ = closure (interior (closure A)) := by
          simpa using
            (closure_interior_closure_interior_closure_eq (A := A))

theorem closure_interior_closure_interior_satisfies_P1
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior (closure (interior (A : Set X))))) := by
  -- `P1` holds for `interior (closure (interior A))`.
  have hP1 : Topology.P1 (interior (closure (interior (A : Set X)))) :=
    Topology.interior_closure_interior_satisfies_P1 (A := A)
  -- `P1` is stable under taking closures.
  exact
    Topology.P1_closure_of_P1
      (A := interior (closure (interior (A : Set X)))) hP1

theorem P3_implies_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A : Set X) → (A ⊆ closure A) := by
  intro hA
  dsimp [Topology.P3] at hA
  exact hA.trans (interior_subset : interior (closure A) ⊆ closure A)

theorem interior_subset_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ interior (closure (interior A)) := by
  -- Apply monotonicity of `interior` to the inclusion
  -- `interior A ⊆ closure (interior A)`.
  have h :
      interior (interior (A : Set X)) ⊆
        interior (closure (interior A)) :=
    interior_mono
      (subset_closure : interior (A : Set X) ⊆ closure (interior A))
  simpa [interior_interior] using h

theorem P3_inter_of_P3_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X))
    (hP3A : Topology.P3 (A : Set X)) (hP3B : Topology.P3 (B : Set X)) :
    Topology.P3 (A ∩ B) := by
  -- `A` and `B` are open because they are closed and satisfy `P3`.
  have hOpenA : IsOpen (A : Set X) :=
    (Topology.open_of_P3_closed (A := A) hA_closed) hP3A
  have hOpenB : IsOpen (B : Set X) :=
    (Topology.open_of_P3_closed (A := B) hB_closed) hP3B
  -- The intersection of open sets is open.
  have hOpenInter : IsOpen (A ∩ B : Set X) := hOpenA.inter hOpenB
  -- Open sets satisfy `P3`.
  exact Topology.open_satisfies_P3 (A := A ∩ B) hOpenInter

theorem P1_iff_exists_open_subset_closure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) ↔
      ∃ U : Set X, IsOpen U ∧ U ⊆ A ∧ closure U = closure A := by
  classical
  constructor
  · intro hP1
    refine ⟨interior (A : Set X), isOpen_interior, interior_subset, ?_⟩
    -- From `P1` we have `closure (interior A) = closure A`.
    have hEq :=
      (Topology.P1_iff_closure_interior_eq_closure (A := A)).1 hP1
    simpa using hEq
  · rintro ⟨U, hOpenU, hUSubA, hClosureEq⟩
    dsimp [Topology.P1]
    intro x hxA
    -- First, place `x` in `closure U` using the equality of closures.
    have hx_clU : x ∈ closure U := by
      have : x ∈ closure (A : Set X) := subset_closure hxA
      simpa [hClosureEq] using this
    -- Since `U ⊆ interior A`, its closure is contained in `closure (interior A)`.
    have hU_in_intA : (U : Set X) ⊆ interior A :=
      interior_maximal hUSubA hOpenU
    have hClSub : closure U ⊆ closure (interior A) :=
      closure_mono hU_in_intA
    exact hClSub hx_clU

theorem P2_inter_of_P2_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X))
    (hP2A : Topology.P2 (A : Set X)) (hP2B : Topology.P2 (B : Set X)) :
    Topology.P2 (A ∩ B) := by
  -- From closedness and `P2`, infer that both `A` and `B` are open.
  have hOpenA : IsOpen (A : Set X) :=
    (Topology.P2_iff_open_of_closed (A := A) hA_closed).1 hP2A
  have hOpenB : IsOpen (B : Set X) :=
    (Topology.P2_iff_open_of_closed (A := B) hB_closed).1 hP2B
  -- The intersection of two open sets is open.
  have hOpenInter : IsOpen (A ∩ B : Set X) := hOpenA.inter hOpenB
  -- Open sets satisfy `P2`.
  exact Topology.open_satisfies_P2 (A := A ∩ B) hOpenInter

theorem subset_interior_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → (A : Set X) ⊆ interior (closure (interior A)) := by
  intro hP2
  dsimp [Topology.P2] at hP2
  exact hP2

theorem subset_interior_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → (A : Set X) ⊆ interior (closure A) := by
  intro hP2
  have hP3 : Topology.P3 (A : Set X) :=
    Topology.P2_implies_P3 (A := A) hP2
  exact Topology.subset_interior_closure_of_P3 (A := A) hP3

theorem interior_union_subset_interior_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ∪ interior B ⊆ interior (closure (A ∪ B : Set X)) := by
  intro x hx
  cases hx with
  | inl hAx =>
      -- First, lift `x ∈ interior A` to `x ∈ interior (A ∪ B)`.
      have hx_int_union : x ∈ interior (A ∪ B) := by
        have hSub : (A : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inl hy
        exact (interior_mono hSub) hAx
      -- Then, use monotonicity of `interior` with `A ∪ B ⊆ closure (A ∪ B)`.
      have hIncl :
          interior (A ∪ B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono (subset_closure : (A ∪ B : Set X) ⊆ closure (A ∪ B))
      exact hIncl hx_int_union
  | inr hBx =>
      -- Symmetric argument for the `B` component.
      have hx_int_union : x ∈ interior (A ∪ B) := by
        have hSub : (B : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inr hy
        exact (interior_mono hSub) hBx
      have hIncl :
          interior (A ∪ B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono (subset_closure : (A ∪ B : Set X) ⊆ closure (A ∪ B))
      exact hIncl hx_int_union

theorem subset_interior_closure_interior_iff_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    ((A : Set X) ⊆ interior (closure (interior A))) ↔ Topology.P2 (A : Set X) := by
  rfl

theorem Topology.interior_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (A : Set X))) ⊆ interior (closure A) := by
  -- From `interior A ⊆ A`, taking closures preserves the inclusion.
  have h : closure (interior (A : Set X)) ⊆ closure A :=
    closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  -- Applying monotonicity of `interior` yields the desired result.
  exact interior_mono h

theorem open_inter_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P1 (A ∩ B) ∧ Topology.P2 (A ∩ B) ∧ Topology.P3 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B : Set X) := hA.inter hB
  exact Topology.open_satisfies_all_Ps (A := A ∩ B) hOpen

theorem open_union_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P1 (A ∪ B) ∧ Topology.P2 (A ∪ B) ∧ Topology.P3 (A ∪ B) := by
  have hOpen : IsOpen (A ∪ B : Set X) := hA.union hB
  exact Topology.open_satisfies_all_Ps (A := A ∪ B) hOpen

theorem clopen_of_P2_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP2 : Topology.P2 (A : Set X)) :
    IsOpen A ∧ IsClosed (A : Set X) := by
  have hOpen : IsOpen (A : Set X) :=
    (Topology.open_of_P2_closed (A := A) hClosed) hP2
  exact And.intro hOpen hClosed

theorem interior_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hIntA =>
      -- `interior A ⊆ interior (A ∪ B)` via monotonicity of `interior`.
      have hIncl : interior (A : Set X) ⊆ interior (A ∪ B) := by
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact hIncl hIntA
  | inr hIntB =>
      -- Symmetric argument for `interior B`.
      have hIncl : interior (B : Set X) ⊆ interior (A ∪ B) := by
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact hIncl hIntB

theorem closure_interior_closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (A : Set X)))) ⊆
      closure (interior (closure A)) := by
  exact
    closure_mono
      (Topology.interior_closure_interior_subset_closure (A := A))

theorem nonempty_interior_closure_of_nonempty_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → A.Nonempty →
      (interior (closure (A : Set X))).Nonempty := by
  intro hP2 hNon
  -- From `P2` we can derive `P3`.
  have hP3 : Topology.P3 (A : Set X) :=
    Topology.P2_implies_P3 (A := A) hP2
  -- Apply the existing lemma for `P3`.
  exact nonempty_interior_closure_of_nonempty_P3 (A := A) hP3 hNon

theorem interior_closure_interior_eq_self_of_open
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (interior (A : Set X)))) :
    interior (closure (interior A)) = closure (interior A) := by
  simpa using hOpen.interior_eq

theorem interior_closure_eq_self_of_open_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    interior (closure (A : Set X)) = closure A := by
  simpa using hOpen.interior_eq

theorem iUnion_closure_subset_closure_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} (S : ι → Set X) :
    (⋃ i, closure (S i) : Set X) ⊆ closure (⋃ i, S i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `S i` is included in the total union.
  have hSub : (S i : Set X) ⊆ ⋃ j, S j := by
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  -- Since `x ∈ closure (S i)` and `S i ⊆ ⋃ j, S j`,
  -- monotonicity of `closure` yields the desired membership.
  have : x ∈ closure (⋃ j, S j) :=
    (closure_mono hSub) hx_i
  exact this

theorem interior_closure_inter_interior_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A ∩ interior B) : Set X)) ⊆ interior (closure A) := by
  -- `A ∩ interior B` is contained in `A`.
  have hSub : (A ∩ interior B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Therefore, the closure of `A ∩ interior B` is contained in the closure of `A`.
  have hClSub : closure (A ∩ interior B : Set X) ⊆ closure A :=
    closure_mono hSub
  -- Applying monotonicity of `interior` yields the desired inclusion.
  exact interior_mono hClSub

theorem P3_iff_interior_eq_self_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P3 (A : Set X) ↔ interior A = A := by
  constructor
  · intro hP3
    exact interior_eq_self_of_P3_closed (A := A) hA hP3
  · intro hIntEq
    -- `A` is open because it coincides with its interior.
    have hOpen : IsOpen (A : Set X) := by
      simpa [hIntEq] using (isOpen_interior : IsOpen (interior (A : Set X)))
    -- Open sets satisfy `P3`.
    simpa [hIntEq] using Topology.open_satisfies_P3 (A := A) hOpen

theorem P2_implies_P3_alt {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P3] at *
  -- `closure (interior A)` sits inside `closure A`.
  have h₁ : closure (interior (A : Set X)) ⊆ closure A :=
    closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  -- Taking interiors preserves the inclusion.
  have h₂ :
      interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h₁
  exact hP2.trans h₂

theorem nonempty_interior_of_nonempty_P3_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X))
    (hP3 : Topology.P3 (A : Set X))
    (hNon : (A : Set X).Nonempty) :
    (interior (A : Set X)).Nonempty := by
  -- From closedness and `P3`, we deduce that `A` is open.
  have hOpen : IsOpen (A : Set X) :=
    (Topology.open_of_P3_closed (A := A) hClosed) hP3
  -- For an open set, its interior equals the set itself.
  have hIntEq : interior (A : Set X) = A := hOpen.interior_eq
  -- Transfer non-emptiness via this equality.
  simpa [hIntEq] using hNon

theorem open_closure_iff_interior_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) ↔
      interior (closure (A : Set X)) = closure A := by
  constructor
  · intro hOpen
    simpa using hOpen.interior_eq
  · intro hEq
    have hOpenInt : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    simpa [hEq] using hOpenInt

theorem P1_implies_P1_of_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) → Topology.P1 (interior A) := by
  intro hP1
  dsimp [Topology.P1] at hP1 ⊢
  intro x hxInt
  -- From `x ∈ interior A`, we know `x ∈ A`.
  have hxA : x ∈ (A : Set X) :=
    (interior_subset : interior A ⊆ A) hxInt
  -- Apply `P1` for `A` to place `x` in `closure (interior A)`.
  have hxCl : x ∈ closure (interior A) := hP1 hxA
  -- Since `interior (interior A) = interior A`, the goal follows directly.
  simpa [interior_interior] using hxCl

theorem P3_and_P2_iff_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    (Topology.P3 (A : Set X) ∧ Topology.P2 A) ↔ Topology.P2 A := by
  constructor
  · intro h
    exact h.2
  · intro hP2
    exact And.intro (Topology.P2_implies_P3 (A := A) hP2) hP2

theorem open_closure_interior_iff_open_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) →
      (IsOpen (closure (interior (A : Set X))) ↔ IsOpen (closure A)) := by
  intro hP2
  -- From `P2`, the two closures coincide.
  have hEq : closure (interior (A : Set X)) = closure A :=
    Topology.P2_implies_closure_interior_eq_closure (A := A) hP2
  -- Trivial equivalence, rewritten using `hEq`.
  have h : IsOpen (closure (interior (A : Set X)))
      ↔ IsOpen (closure (interior (A : Set X))) := Iff.rfl
  simpa [hEq] using h

theorem open_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) →
      IsOpen (closure (A : Set X)) →
        IsOpen (closure (interior A)) := by
  intro hP1 hOpen
  -- From `P1`, we obtain the equality of closures.
  have hEq : closure (interior (A : Set X)) = closure A :=
    (Topology.P1_iff_closure_interior_eq_closure (A := A)).1 hP1
  -- Rewrite using this equality to transfer openness.
  simpa [hEq] using hOpen

theorem open_closure_interior_iff_interior_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (interior (A : Set X))) ↔
      interior (closure (interior A)) = closure (interior A) := by
  constructor
  · intro hOpen
    simpa using hOpen.interior_eq
  · intro hEq
    have hOpenInt : IsOpen (interior (closure (interior (A : Set X)))) := isOpen_interior
    simpa [hEq] using hOpenInt

theorem open_closure_interior_eq_closure_implies_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (interior (A : Set X))))
    (hEq  : closure (interior (A : Set X)) = closure A) :
    Topology.P3 (A : Set X) := by
  dsimp [Topology.P3]
  intro x hxA
  -- First, place `x` inside `closure (interior A)` using the equality of closures.
  have hx_clInt : x ∈ closure (interior (A : Set X)) := by
    have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
    simpa [hEq] using hx_cl
  -- Since this set is open, its interior equals itself.
  have hx_int_clInt :
      x ∈ interior (closure (interior (A : Set X))) := by
    simpa [hOpen.interior_eq] using hx_clInt
  -- The equality of closures yields an equality of their interiors.
  have hIntEq :
      interior (closure (interior (A : Set X))) =
        interior (closure (A : Set X)) := by
    simpa using congrArg interior hEq
  -- Reinterpret the membership in the desired interior.
  have hx_int : x ∈ interior (closure (A : Set X)) := by
    simpa [hIntEq] using hx_int_clInt
  exact hx_int

theorem closure_interior_subset_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    closure (interior (A : Set X)) ⊆ A := by
  -- `interior A` is contained in `A`, hence its closure is contained in `closure A`.
  have hSub : closure (interior (A : Set X)) ⊆ closure A :=
    closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  -- Since `A` is closed, `closure A = A`.
  simpa [hA.closure_eq] using hSub

theorem interior_closure_closure_interior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (closure (interior (A : Set X))))
      = interior (closure (interior A)) := by
  simpa [closure_closure]

theorem closure_interior_eq_empty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) = (∅ : Set X) ↔ interior A = ∅ := by
  constructor
  · intro h
    have hSub : interior (A : Set X) ⊆ (∅ : Set X) := by
      have : interior (A : Set X) ⊆ closure (interior A) := subset_closure
      simpa [h] using this
    exact Set.Subset.antisymm hSub (Set.empty_subset _)
  · intro h
    simpa [h, closure_empty]

theorem closure_interior_eq_self_of_P3_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (A : Set X)) :
    closure (interior (A : Set X)) = A := by
  -- First, `interior A = A` because `A` is closed and satisfies `P3`.
  have hInt : interior (A : Set X) = A :=
    interior_eq_self_of_P3_closed (A := A) hA_closed hP3
  -- Taking closures and rewriting yields the desired equality.
  simpa [hInt, hA_closed.closure_eq]

theorem iUnion_open_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {S : ι → Set X}
    (hS : ∀ i, IsOpen (S i)) :
    Topology.P1 (⋃ i, S i) ∧ Topology.P2 (⋃ i, S i) ∧ Topology.P3 (⋃ i, S i) := by
  have hOpen : IsOpen (⋃ i, S i : Set X) := by
    simpa using isOpen_iUnion (fun i => hS i)
  exact Topology.open_satisfies_all_Ps (A := ⋃ i, S i) hOpen

theorem closure_union_interior_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∪ interior B) ⊆
      closure (interior (A ∪ B)) := by
  exact
    closure_mono
      (Topology.interior_union_subset (A := A) (B := B))

theorem interior_closure_interior_interior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (interior (A : Set X)))) =
      interior (closure (interior A)) := by
  simpa [interior_interior]

theorem closure_interior_univ_eq_univ {X : Type*} [TopologicalSpace X] :
    closure (interior (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [interior_univ, closure_univ]

theorem interior_closure_union_satisfies_P3
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 (interior (closure (A : Set X)) ∪ interior (closure B)) := by
  -- `interior (closure A)` and `interior (closure B)` are both open.
  have hOpenA : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  have hOpenB : IsOpen (interior (closure (B : Set X))) := isOpen_interior
  -- Their union is therefore open.
  have hOpen : IsOpen (interior (closure (A : Set X)) ∪ interior (closure B)) :=
    hOpenA.union hOpenB
  -- Any open set satisfies `P3`.
  exact Topology.open_satisfies_P3
    (A := interior (closure (A : Set X)) ∪ interior (closure B)) hOpen

theorem iUnion_interior_subset_interior_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} (S : ι → Set X) :
    (⋃ i, interior (S i) : Set X) ⊆ interior (⋃ i, S i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_int⟩
  -- `S i ⊆ ⋃ j, S j`
  have hSub : (S i : Set X) ⊆ ⋃ j, S j := by
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  -- Monotonicity of `interior` lifts the inclusion.
  have hIntSub : interior (S i) ⊆ interior (⋃ j, S j) :=
    interior_mono hSub
  exact hIntSub hx_int

theorem union_interior_closure_interior_subset_interior_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A : Set X))) ∪
        interior (closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- Show that `interior (closure (interior A))` is included in the target.
      have hIncl :
          closure (interior (A : Set X))
            ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      have hIntIncl :
          interior (closure (interior (A : Set X)))
            ⊆ interior (closure (interior (A ∪ B))) :=
        interior_mono hIncl
      exact hIntIncl hxA
  | inr hxB =>
      -- Symmetric argument for the `B` component.
      have hIncl :
          closure (interior (B : Set X))
            ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      have hIntIncl :
          interior (closure (interior (B : Set X)))
            ⊆ interior (closure (interior (A ∪ B))) :=
        interior_mono hIncl
      exact hIntIncl hxB

theorem interior_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior ((A \ B) : Set X) ⊆ interior A := by
  -- Since `A \ B ⊆ A`, monotonicity of `interior` yields the desired inclusion.
  have hSub : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  exact interior_mono hSub

theorem P1_implies_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) → (A ⊆ closure (interior (closure A))) := by
  intro hP1
  dsimp [Topology.P1] at hP1
  intro x hxA
  -- From `P1`, we have `x ∈ closure (interior A)`.
  have hx_cl : x ∈ closure (interior (A : Set X)) := hP1 hxA
  -- Monotonicity of `interior` lifts `A ⊆ closure A`.
  have hIncl :
      closure (interior (A : Set X)) ⊆
        closure (interior (closure (A : Set X))) := by
    apply closure_mono
    apply interior_mono
    exact (subset_closure : (A : Set X) ⊆ closure A)
  exact hIncl hx_cl

theorem closed_of_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) = A → IsClosed (A : Set X) := by
  intro hEq
  simpa [hEq] using
    (isClosed_closure :
      IsClosed (closure (interior (A : Set X))))

theorem closure_union_subset_closure_of_subset
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : (A : Set X) ⊆ C) (hB : (B : Set X) ⊆ C) :
    closure (A ∪ B : Set X) ⊆ closure C := by
  exact closure_mono (by
    intro x hx
    cases hx with
    | inl hAx => exact hA hAx
    | inr hBx => exact hB hBx)

theorem closure_interiors_subset_closure_interior_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((interior (A : Set X)) ∩ interior B)
      ⊆ closure (interior (A ∩ B)) := by
  -- First, show that `interior A ∩ interior B ⊆ interior (A ∩ B)`.
  have hSub :
      ((interior (A : Set X)) ∩ interior B : Set X) ⊆
        interior (A ∩ B) := by
    intro x hx
    -- `interior A ∩ interior B` is an open set contained in `A ∩ B`.
    have hOpen : IsOpen ((interior (A : Set X)) ∩ interior B) :=
      (isOpen_interior).inter isOpen_interior
    have hIncl :
        ((interior (A : Set X)) ∩ interior B : Set X) ⊆ (A ∩ B) := by
      intro y hy
      exact
        And.intro
          ((interior_subset : interior A ⊆ A) hy.1)
          ((interior_subset : interior B ⊆ B) hy.2)
    -- Apply `interior_maximal` to place `x` in `interior (A ∩ B)`.
    have : x ∈ interior (A ∩ B) :=
      (interior_maximal hIncl hOpen) hx
    exact this
  -- Finally, lift the inclusion through `closure`.
  exact closure_mono hSub

theorem interior_closure_subset_closure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    interior (closure (A : Set X)) ⊆ closure B := by
  -- First, upgrade the inclusion through `closure` and `interior`.
  have h₁ :
      interior (closure (A : Set X)) ⊆ interior (closure B) :=
    interior_closure_mono (A := A) (B := B) hAB
  -- Second, use that the interior of any set is contained in the set itself.
  exact h₁.trans (interior_subset : interior (closure B) ⊆ closure B)

theorem P2_implies_P1_of_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 (interior A) := by
  intro hP2
  -- Derive `P1` for `A` from `P2`.
  have hP1 : Topology.P1 (A : Set X) :=
    Topology.P2_implies_P1 (A := A) hP2
  -- Transfer `P1` from `A` to its interior.
  exact Topology.P1_implies_P1_of_interior (A := A) hP1

theorem interior_closure_interior_closure_satisfies_P1
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (interior (closure (A : Set X))))) := by
  simpa using
    (Topology.interior_closure_interior_satisfies_P1
      (A := closure (A : Set X)))

theorem P2_union_of_P2_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P2 (A ∪ B) := by
  have hB₂ : Topology.P2 (B : Set X) :=
    Topology.open_satisfies_P2 (A := B) hB
  exact Topology.P2_union_of_P2 (A := A) (B := B) hA hB₂

theorem P1_union_of_P1_and_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP1A : Topology.P1 (A : Set X)) (hOpenB : IsOpen (B : Set X)) :
    Topology.P1 (A ∪ B) := by
  -- `B` is open, hence satisfies `P1`.
  have hP1B : Topology.P1 (B : Set X) :=
    Topology.open_satisfies_P1 (A := B) hOpenB
  -- Apply the union lemma for two sets satisfying `P1`.
  exact Topology.P1_union_of_P1 (A := A) (B := B) hP1A hP1B

theorem P1_sUnion_of_P1
    {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → Topology.P1 (A : Set X)) :
    Topology.P1 (⋃₀ 𝒜 : Set X) := by
  dsimp [Topology.P1] at h𝒜 ⊢
  intro x hx
  -- Find a set `A ∈ 𝒜` that contains `x`.
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  -- Apply `P1` for this particular set `A`.
  have hA_P1 : Topology.P1 (A : Set X) := h𝒜 A hA_mem
  have hx_cl : x ∈ closure (interior (A : Set X)) := hA_P1 hxA
  -- Show that the closure of `interior A` is contained in the closure of
  -- `interior (⋃₀ 𝒜)`.
  have hIncl :
      closure (interior (A : Set X)) ⊆
        closure (interior (⋃₀ 𝒜 : Set X)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  -- Conclude the desired membership.
  exact hIncl hx_cl

theorem P2_sUnion_of_P2
    {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → Topology.P2 (A : Set X)) :
    Topology.P2 (⋃₀ 𝒜 : Set X) := by
  dsimp [Topology.P2] at h𝒜 ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  -- Apply `P2` for the particular set `A`.
  have hx_intA : x ∈ interior (closure (interior (A : Set X))) :=
    (h𝒜 A hA_mem) hxA
  -- Show that this interior is contained in the target interior.
  have hIncl :
      closure (interior (A : Set X)) ⊆
        closure (interior (⋃₀ 𝒜 : Set X)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  have hIntIncl :
      interior (closure (interior (A : Set X))) ⊆
        interior (closure (interior (⋃₀ 𝒜 : Set X))) :=
    interior_mono hIncl
  exact hIntIncl hx_intA

theorem P2_iff_P1_and_P3_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  constructor
  · intro hP2
    exact And.intro
      (Topology.P2_implies_P1 (A := A) hP2)
      (Topology.P2_implies_P3 (A := A) hP2)
  · rintro ⟨hP1, _hP3⟩
    exact ((Topology.P1_iff_P2_of_isOpen (A := A) hA).1) hP1

theorem P2_closure_implies_P1_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → Topology.P1 (closure A) := by
  intro hP2
  have hP1 : Topology.P1 (closure (A : Set X)) :=
    Topology.P2_implies_P1 (A := closure (A : Set X)) hP2
  simpa using hP1

theorem P3_sUnion_of_P3
    {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → Topology.P3 (A : Set X)) :
    Topology.P3 (⋃₀ 𝒜 : Set X) := by
  dsimp [Topology.P3] at h𝒜 ⊢
  intro x hx
  -- Choose a witness set `A ∈ 𝒜` such that `x ∈ A`.
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  -- Apply `P3` for this particular set `A`.
  have hx_intA : x ∈ interior (closure (A : Set X)) :=
    (h𝒜 A hA_mem) hxA
  -- Show that `interior (closure A)` is contained in the desired interior.
  have hIncl :
      closure (A : Set X) ⊆ closure (⋃₀ 𝒜 : Set X) := by
    apply closure_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  have hIntIncl :
      interior (closure (A : Set X)) ⊆
        interior (closure (⋃₀ 𝒜 : Set X)) :=
    interior_mono hIncl
  exact hIntIncl hx_intA

theorem interior_closure_interior_eq_univ_implies_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (A : Set X))) = (Set.univ : Set X) →
      Topology.P2 (A : Set X) := by
  intro hUniv
  dsimp [Topology.P2]
  intro x hxA
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hUniv] using this

theorem open_closure_interior_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (interior (A : Set X)))) :
    Topology.P1 (closure (interior A))
      ∧ Topology.P2 (closure (interior A))
      ∧ Topology.P3 (closure (interior A)) := by
  simpa using
    Topology.open_satisfies_all_Ps
      (A := closure (interior (A : Set X))) hOpen

theorem P3_union_of_P3_and_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP3A : Topology.P3 (A : Set X)) (hOpenB : IsOpen (B : Set X)) :
    Topology.P3 (A ∪ B) := by
  -- `B` is open, hence satisfies `P3`.
  have hP3B : Topology.P3 (B : Set X) :=
    Topology.open_satisfies_P3 (A := B) hOpenB
  -- Apply the existing union lemma for two sets satisfying `P3`.
  exact Topology.P3_union_of_P3 (A := A) (B := B) hP3A hP3B

theorem closure_interior_closure_interior_closure_interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure (interior (closure (A : Set X))))))))) =
      closure (interior (closure A)) := by
  simp [closure_interior_closure_interior_closure_eq,
        closure_closure, interior_interior]

theorem P3_iff_P1_and_P2_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P3 (A : Set X) ↔ (Topology.P1 A ∧ Topology.P2 A) := by
  -- Existing equivalences on open sets.
  have h3_2 : Topology.P3 (A : Set X) ↔ Topology.P2 A :=
    Topology.P3_iff_P2_of_isOpen (A := A) hA
  have h1_2 : Topology.P1 (A : Set X) ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  constructor
  · intro hP3
    -- Derive `P2` from `P3`, then `P1` from `P2`.
    have hP2 : Topology.P2 (A : Set X) := (h3_2).1 hP3
    have hP1 : Topology.P1 (A : Set X) := (h1_2).2 hP2
    exact And.intro hP1 hP2
  · rintro ⟨_hP1, hP2⟩
    -- Convert `P2` back to `P3`.
    exact (h3_2).2 hP2

theorem P3_closure_iff_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) ↔ closure A ⊆ interior (closure A) := by
  dsimp [Topology.P3]
  simpa [closure_closure]

theorem closure_iInter_subset_iInter_closure
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {S : ι → Set X} :
    closure (⋂ i, S i : Set X) ⊆ (⋂ i, closure (S i) : Set X) := by
  intro x hx
  -- For each index `i`, derive `x ∈ closure (S i)`.
  have hx_i : ∀ i, x ∈ closure (S i) := by
    intro i
    -- The intersection is contained in each component `S i`.
    have hSub : (⋂ j, S j : Set X) ⊆ S i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Monotonicity of `closure` lifts this inclusion.
    have hIncl : closure (⋂ j, S j : Set X) ⊆ closure (S i) :=
      closure_mono hSub
    exact hIncl hx
  -- Combine the individual memberships into one for the intersection of closures.
  exact (Set.mem_iInter.2 hx_i)

theorem closure_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((A \ B) : Set X) ⊆ closure A := by
  -- Since `A \ B ⊆ A`, the monotonicity of `closure` gives the result.
  exact closure_mono (by
    intro x hx
    exact hx.1)

theorem closure_interior_empty_eq_empty {X : Type*} [TopologicalSpace X] :
    closure (interior (∅ : Set X)) = (∅ : Set X) := by
  simp

theorem open_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    (A : Set X) ⊆ interior (closure A) := by
  exact interior_maximal subset_closure hA

theorem closure_interior_eq_self_of_P2_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P2 (A : Set X) → closure (interior A) = A := by
  intro hP2
  -- `interior A = A` because `A` is closed and satisfies `P2`.
  have hInt : interior A = A :=
    (interior_eq_self_of_P2_closed (A := A) hA) hP2
  -- Apply `closure` to both sides and rewrite using `hA.closure_eq`.
  have hClos : closure (interior A) = closure A :=
    congrArg closure hInt
  simpa [hA.closure_eq] using hClos

theorem interior_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ closure (interior A) := by
  simpa using
    (subset_closure :
      interior (A : Set X) ⊆ closure (interior A))

theorem interior_closure_iInter_subset_iInter_interior_closure
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {S : ι → Set X} :
    interior (closure (⋂ i, S i : Set X)) ⊆ ⋂ i, interior (closure (S i)) := by
  classical
  intro x hx
  -- For each index `i`, show that `x` belongs to `interior (closure (S i))`.
  have hx_i : ∀ i, x ∈ interior (closure (S i)) := by
    intro i
    -- `⋂ i, S i ⊆ S i`, hence their closures satisfy the same inclusion.
    have hSub : closure (⋂ j, S j : Set X) ⊆ closure (S i) := by
      apply closure_mono
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Monotonicity of `interior` turns this into an inclusion of interiors.
    have hIncl :
        interior (closure (⋂ j, S j : Set X))
          ⊆ interior (closure (S i)) :=
      interior_mono hSub
    exact hIncl hx
  -- Combine the pointwise memberships into one for the intersection.
  exact Set.mem_iInter.2 hx_i

theorem P1_iff_P2_of_open_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    Topology.P1 (closure (A : Set X)) ↔ Topology.P2 (closure (A : Set X)) := by
  simpa using
    (Topology.P1_iff_P2_of_isOpen (A := closure (A : Set X)) hOpen)

theorem all_Ps_iff_P2_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    (Topology.P1 (A : Set X) ∧ Topology.P2 A ∧ Topology.P3 A) ↔ Topology.P2 A := by
  constructor
  · intro h
    exact h.2.1
  · intro hP2
    have hP1 : Topology.P1 (A : Set X) :=
      (Topology.P1_iff_P2_of_isOpen (A := A) hA).2 hP2
    have hP3 : Topology.P3 (A : Set X) :=
      (Topology.P3_iff_P2_of_isOpen (A := A) hA).2 hP2
    exact And.intro hP1 (And.intro hP2 hP3)

theorem interior_closure_interior_inter_subset_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior ((A ∩ B) : Set X)))
      ⊆ interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  -- First component: `x ∈ interior (closure (interior A))`.
  have hxA : x ∈ interior (closure (interior A)) := by
    -- Show the required set inclusion and apply `hx`.
    have hIncl :
        closure (interior ((A ∩ B) : Set X))
          ⊆ closure (interior A) := by
      apply closure_mono
      intro y hy
      -- From `y ∈ interior (A ∩ B)` deduce `y ∈ interior A`.
      have hPair := (interior_inter_subset (A := A) (B := B)) hy
      exact hPair.1
    exact (interior_mono hIncl) hx
  -- Second component: `x ∈ interior (closure (interior B))`.
  have hxB : x ∈ interior (closure (interior B)) := by
    -- Analogous argument with `B`.
    have hIncl :
        closure (interior ((A ∩ B) : Set X))
          ⊆ closure (interior B) := by
      apply closure_mono
      intro y hy
      have hPair := (interior_inter_subset (A := A) (B := B)) hy
      exact hPair.2
    exact (interior_mono hIncl) hx
  exact And.intro hxA hxB

theorem open_closure_implies_P3_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    Topology.P3 (closure (A : Set X)) := by
  simpa using
    (Topology.open_satisfies_P3 (A := closure (A : Set X)) hOpen)

theorem interior_closure_inter_satisfies_P1
    {X : Type*} [TopologicalSpace X] (A B : Set X) :
    Topology.P1 (interior (closure ((A ∩ B) : Set X))) := by
  simpa using
    (Topology.interior_closure_satisfies_P1 (A := (A ∩ B)))

theorem interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ closure A := by
  exact interior_subset.trans subset_closure

theorem all_Ps_iff_P3_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    (Topology.P1 (A : Set X) ∧ Topology.P2 A ∧ Topology.P3 A) ↔ Topology.P3 A := by
  constructor
  · intro h
    exact h.2.2
  · intro hP3
    -- From `P3` and openness we obtain `P2`.
    have hP2 : Topology.P2 (A : Set X) :=
      (Topology.P3_iff_P2_of_isOpen (A := A) hA).1 hP3
    -- `P2` implies `P1`.
    have hP1 : Topology.P1 (A : Set X) :=
      Topology.P2_implies_P1 (A := A) hP2
    exact And.intro hP1 (And.intro hP2 hP3)

theorem interior_inter_eq_of_open {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior ((A ∩ B) : Set X) = interior A ∩ interior B := by
  -- `A ∩ B` is open because it is the intersection of two open sets.
  have hOpen : IsOpen ((A ∩ B) : Set X) := hA.inter hB
  -- The interior of an open set is the set itself.
  simpa [hA.interior_eq, hB.interior_eq, hOpen.interior_eq]

theorem closureInterior_inter_self_eq_self_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) → (closure (interior A) ∩ A = A) := by
  intro hP1
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.2
  · intro x hxA
    have hxCl : x ∈ closure (interior (A : Set X)) := hP1 hxA
    exact And.intro hxCl hxA

theorem interior_inter_of_isOpen_right
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsOpen (B : Set X)) :
    interior ((A ∩ B) : Set X) = interior A ∩ B := by
  apply Set.Subset.antisymm
  · intro x hx
    have hA : x ∈ interior A := by
      -- `A ∩ B ⊆ A`
      have hSub : (A ∩ B : Set X) ⊆ A := by
        intro y hy
        exact hy.1
      exact (interior_mono hSub) hx
    have hBmem : x ∈ B := by
      have : x ∈ (A ∩ B : Set X) :=
        (interior_subset : interior (A ∩ B) ⊆ A ∩ B) hx
      exact this.2
    exact And.intro hA hBmem
  · intro x hx
    rcases hx with ⟨hIntA, hBx⟩
    -- `x` lies in `interior A ∩ B`
    have hxInter : x ∈ interior A ∩ B := And.intro hIntA hBx
    -- `interior A ∩ B` is open
    have hOpen : IsOpen (interior A ∩ B) :=
      (isOpen_interior).inter hB
    -- Inclusion `interior A ∩ B ⊆ A ∩ B`
    have hSub : (interior A ∩ B : Set X) ⊆ A ∩ B := by
      intro y hy
      exact
        And.intro
          ((interior_subset : interior A ⊆ A) hy.1)
          hy.2
    -- Place `x` inside `interior (A ∩ B)`
    have : x ∈ interior (A ∩ B) :=
      (interior_maximal hSub hOpen) hxInter
    exact this

theorem closure_interior_inter_eq_closure_inter_of_open
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    closure (interior ((A ∩ B) : Set X)) = closure (A ∩ B) := by
  -- The intersection of two open sets is open.
  have hOpen : IsOpen ((A ∩ B) : Set X) := hA.inter hB
  -- For an open set, its interior equals the set itself.
  have hInt : interior ((A ∩ B) : Set X) = A ∩ B := hOpen.interior_eq
  simpa [hInt]

theorem P2_and_open_closure_interior_implies_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) →
      IsOpen (closure (interior (A : Set X))) →
      Topology.P3 (A : Set X) := by
  intro hP2 hOpen
  -- `P2` yields the equality of the two closures.
  have hEq : closure (interior (A : Set X)) = closure A :=
    Topology.P2_implies_closure_interior_eq_closure (A := A) hP2
  -- Combine openness with the equality to obtain `P3`.
  exact
    Topology.open_closure_interior_eq_closure_implies_P3
      (A := A) hOpen hEq

theorem P3_and_interiors_equal_implies_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A : Set X) →
      interior (closure (A : Set X)) = interior (closure (interior A)) →
      Topology.P2 A := by
  intro hP3 hEq
  dsimp [Topology.P2] at *
  intro x hxA
  have hxInt : x ∈ interior (closure (A : Set X)) := hP3 hxA
  simpa [hEq] using hxInt

theorem closure_iUnion_interior_subset_closure_interior_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} (S : ι → Set X) :
    closure (⋃ i, interior (S i) : Set X) ⊆
      closure (interior (⋃ i, S i)) := by
  have hSub :
      (⋃ i, interior (S i) : Set X) ⊆ interior (⋃ i, S i) :=
    iUnion_interior_subset_interior_iUnion (S := S)
  exact closure_mono hSub

theorem sUnion_open_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → IsOpen (A : Set X)) :
    Topology.P1 (⋃₀ 𝒜 : Set X) ∧ Topology.P2 (⋃₀ 𝒜) ∧ Topology.P3 (⋃₀ 𝒜) := by
  classical
  -- First, show that the `sUnion` is an open set.
  have hOpen : IsOpen (⋃₀ 𝒜 : Set X) := by
    -- Re-express `⋃₀ 𝒜` as an `iUnion` over a subtype and apply `isOpen_iUnion`.
    simpa [Set.sUnion_eq_iUnion] using
      isOpen_iUnion (fun A : {B : Set X // B ∈ 𝒜} =>
        h𝒜 A A.property)
  -- Open sets satisfy all three properties simultaneously.
  simpa using
    Topology.open_satisfies_all_Ps (A := ⋃₀ 𝒜) hOpen

theorem interior_closure_inter_closure_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A ∩ closure B) : Set X)) ⊆ interior (closure A) := by
  intro x hx
  -- Since `A ∩ closure B ⊆ A`, their closures satisfy the same inclusion.
  have hSub : closure ((A ∩ closure B) : Set X) ⊆ closure A := by
    apply closure_mono
    intro y hy
    exact hy.1
  -- Monotonicity of `interior` gives the desired inclusion.
  exact (interior_mono hSub) hx

theorem all_Ps_iff_P1_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    (Topology.P1 (A : Set X) ∧ Topology.P2 A ∧ Topology.P3 A) ↔ Topology.P1 A := by
  constructor
  · intro h
    exact h.1
  · intro hP1
    have hP2 : Topology.P2 (A : Set X) :=
      (Topology.P1_iff_P2_of_isOpen (A := A) hA).1 hP1
    have hP3 : Topology.P3 (A : Set X) :=
      (Topology.P1_iff_P3_of_isOpen (A := A) hA).1 hP1
    exact And.intro hP1 (And.intro hP2 hP3)

theorem open_closure_iff_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) ↔
      closure (A : Set X) ⊆ interior (closure A) := by
  constructor
  · intro hOpen
    -- For an open set, its interior equals itself.
    have hEq : interior (closure (A : Set X)) = closure A :=
      hOpen.interior_eq
    -- Rewrite the reflexive inclusion using this equality.
    simpa [hEq] using
      (subset_rfl : closure (A : Set X) ⊆ closure A)
  · intro hSub
    -- Upgrade the given inclusion to an equality.
    have hEq : interior (closure (A : Set X)) = closure A :=
      Set.Subset.antisymm interior_subset hSub
    -- The interior of any set is open; use this to conclude.
    have hOpenInt : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    simpa [hEq] using hOpenInt

theorem open_inter_satisfies_P2 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P2 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B : Set X) := hA.inter hB
  exact Topology.open_satisfies_P2 (A := A ∩ B) hOpen

theorem closure_interior_eq_self_of_P1_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P1 (A : Set X) → closure (interior A) = A := by
  intro hP1
  exact
    (Topology.P1_iff_closure_interior_eq_self_of_closed
        (A := A) hA).1 hP1

theorem interior_closure_eq_interior_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed (A : Set X)) :
    interior (closure (A : Set X)) = interior A := by
  simpa [hA.closure_eq]

theorem P1_of_interior_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior (A : Set X) = A) : Topology.P1 A := by
  -- From the hypothesis we infer that `A` is open.
  have hOpen : IsOpen (A : Set X) := by
    simpa [hInt] using (isOpen_interior : IsOpen (interior (A : Set X)))
  -- Open sets satisfy `P1`.
  exact Topology.open_satisfies_P1 (A := A) hOpen

theorem P1_iff_closureInterior_inter_self_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) ↔ closure (interior A) ∩ A = A := by
  constructor
  · intro hP1
    exact closureInterior_inter_self_eq_self_of_P1 (A := A) hP1
  · intro hEq
    dsimp [Topology.P1]
    intro x hxA
    -- Using the assumed equality to place `x` in the required closure.
    have hxInter : x ∈ closure (interior (A : Set X)) ∩ A := by
      simpa [hEq] using hxA
    exact hxInter.1

theorem interior_inter_closure_eq_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∩ closure A = interior A := by
  have h : interior (A : Set X) ⊆ closure A :=
    interior_subset.trans subset_closure
  simpa [Set.inter_eq_left.mpr h]

theorem P2_and_interior_closure_empty_implies_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) →
      interior (closure (A : Set X)) = ∅ →
      A = ∅ := by
  intro hP2 hIntEmpty
  -- Derive `P3` from `P2`.
  have hP3 : Topology.P3 (A : Set X) :=
    Topology.P2_implies_P3 (A := A) hP2
  -- Apply the existing lemma for `P3`.
  exact
    Topology.P3_and_interior_closure_empty_implies_empty
      (A := A) hP3 hIntEmpty

theorem P3_implies_P2_of_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A : Set X) → Topology.P2 (interior A) := by
  intro _
  exact Topology.open_satisfies_P2 (A := interior A) isOpen_interior

theorem open_inter_satisfies_P1
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P1 (A ∩ B) := by
  -- The intersection of two open sets is open.
  have hOpen : IsOpen ((A ∩ B) : Set X) := hA.inter hB
  -- Open sets satisfy `P1`.
  exact Topology.open_satisfies_P1 (A := A ∩ B) hOpen

theorem all_Ps_iff_P2_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    (Topology.P1 (A : Set X) ∧ Topology.P2 A ∧ Topology.P3 A) ↔ Topology.P2 A := by
  constructor
  · intro h
    exact h.2.1
  · intro hP2
    have hP1 : Topology.P1 (A : Set X) :=
      Topology.P2_implies_P1_of_closed (A := A) hA hP2
    have hP3 : Topology.P3 (A : Set X) :=
      Topology.P2_implies_P3_of_closed (A := A) hA hP2
    exact And.intro hP1 (And.intro hP2 hP3)

theorem interior_inter_of_isOpen_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) :
    interior ((A ∩ B) : Set X) = A ∩ interior B := by
  simpa [Set.inter_comm] using
    (interior_inter_of_isOpen_right (A := B) (B := A) hA)

theorem interior_union_eq_of_open
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior ((A ∪ B) : Set X) = interior A ∪ interior B := by
  -- The interiors of open sets coincide with the sets themselves.
  have hIntA : interior (A : Set X) = A := hA.interior_eq
  have hIntB : interior (B : Set X) = B := hB.interior_eq
  -- The union of two open sets is open, hence its interior is itself.
  have hIntUnion : interior (A ∪ B : Set X) = A ∪ B :=
    (hA.union hB).interior_eq
  simpa [hIntA, hIntB, hIntUnion]

theorem P1_and_closure_interior_empty_implies_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) →
      closure (interior (A : Set X)) = (∅ : Set X) → A = ∅ := by
  intro hP1 hClosEmpty
  -- `closure (interior A) = ∅` implies `interior A = ∅`.
  have hIntEmpty : interior (A : Set X) = ∅ :=
    ((closure_interior_eq_empty_iff (A := A)).1 hClosEmpty)
  -- Apply the existing lemma that uses the emptiness of `interior A`.
  exact
    Topology.P1_and_interior_empty_implies_empty
      (A := A) hP1 hIntEmpty

theorem closure_inter_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    (closure (A : Set X) ∩ interior (closure A))
      = interior (closure A) := by
  -- `interior (closure A)` is contained in `closure A`.
  have h : interior (closure (A : Set X)) ⊆ closure A := interior_subset
  -- Use the set-theoretic lemma `inter_eq_right` to obtain the equality.
  exact Set.inter_eq_right.mpr h

theorem open_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (closure (A : Set X))) (hB : IsOpen (closure B)) :
    IsOpen (closure (A ∪ B : Set X)) := by
  have h : IsOpen (closure A ∪ closure B) := hA.union hB
  simpa [closure_union] using h

theorem closure_union_subset_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) ∪ closure B ⊆ closure (A ∪ B : Set X) := by
  intro x hx
  cases hx with
  | inl hAx =>
      -- `closure A ⊆ closure (A ∪ B)` via monotonicity of `closure`.
      have hIncl : closure (A : Set X) ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inl hy
      exact hIncl hAx
  | inr hBx =>
      -- Symmetric argument for `closure B`.
      have hIncl : closure (B : Set X) ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inr hy
      exact hIncl hBx

theorem interior_closure_inter_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) ∩ closure (interior A) ⊆ closure A := by
  intro x hx
  -- The first component places `x` in `interior (closure A)`.
  have hInt : x ∈ interior (closure (A : Set X)) := hx.1
  -- The interior of any set is contained in the set itself.
  have hIncl : interior (closure (A : Set X)) ⊆ closure A :=
    interior_subset
  -- Conclude the desired membership.
  exact hIncl hInt

theorem open_closure_iff_all_Ps
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) ↔
      (Topology.P1 (closure A) ∧ Topology.P2 (closure A) ∧ Topology.P3 (closure A)) := by
  constructor
  · intro hOpen
    exact Topology.open_closure_satisfies_all_Ps (A := A) hOpen
  · rintro ⟨hP1, hP2, hP3⟩
    -- `P3` for `closure A` is equivalent to openness of `closure A`.
    have hOpen : IsOpen (closure (A : Set X)) :=
      (Topology.P3_closure_iff_open_closure (A := A)).1 (by
        simpa using hP3)
    exact hOpen

theorem P1_implies_P2_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 (A : Set X) → Topology.P2 A := by
  intro hP1
  have hEquiv := (Topology.P1_iff_P2_of_isOpen (A := A) hA)
  exact hEquiv.1 hP1

theorem subset_closure_interior_iff_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    ((A : Set X) ⊆ closure (interior A)) ↔ Topology.P1 (A : Set X) := by
  rfl

theorem closure_interior_iUnion_eq_closure_iUnion_of_open
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {S : ι → Set X}
    (hS : ∀ i, IsOpen (S i)) :
    closure (interior ((⋃ i, S i) : Set X)) = closure (⋃ i, S i) := by
  -- The union of open sets is open.
  have hOpen : IsOpen ((⋃ i, S i) : Set X) := by
    simpa using isOpen_iUnion (fun i => hS i)
  -- For an open set, its interior equals itself.
  have hInt : interior ((⋃ i, S i) : Set X) = ⋃ i, S i := hOpen.interior_eq
  simpa [hInt]

theorem isOpen_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsOpen (interior (closure (A : Set X))) := by
  simpa using
    (isOpen_interior : IsOpen (interior (closure (A : Set X))))

theorem closure_inter_interior_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((A ∩ interior B) : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  -- Inclusion into `closure A`.
  have hA : closure ((A ∩ interior B) : Set X) ⊆ closure A := by
    apply closure_mono
    intro y hy
    exact hy.1
  -- Inclusion into `closure B`.
  have hB : closure ((A ∩ interior B) : Set X) ⊆ closure B := by
    apply closure_mono
    intro y hy
    exact (interior_subset : interior B ⊆ B) hy.2
  exact And.intro (hA hx) (hB hx)

theorem closure_interior_eq_univ_of_dense_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (A : Set X))
    (hDense : closure (A : Set X) = (Set.univ : Set X)) :
    closure (interior (A : Set X)) = (Set.univ : Set X) := by
  -- From `P1`, we know `closure (interior A) = closure A`.
  have hEq : closure (interior (A : Set X)) = closure A :=
    (Topology.P1_iff_closure_interior_eq_closure (A := A)).1 hP1
  -- Combine this with the density hypothesis to obtain the result.
  simpa [hDense] using hEq

theorem interior_iInter_subset_iInter_interior
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {S : ι → Set X} :
    interior (⋂ i, S i : Set X) ⊆ ⋂ i, interior (S i) := by
  intro x hx
  -- For each index `i`, show `x ∈ interior (S i)`.
  have hx_i : ∀ i, x ∈ interior (S i) := by
    intro i
    -- The intersection is contained in `S i`.
    have hSub : (⋂ j, S j : Set X) ⊆ S i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Apply monotonicity of `interior`.
    have hIncl : interior (⋂ j, S j : Set X) ⊆ interior (S i) :=
      interior_mono hSub
    exact hIncl hx
  -- Combine the pointwise fact into membership in the intersection of interiors.
  exact Set.mem_iInter.2 hx_i

theorem open_inter_satisfies_P3
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P3 (A ∩ B) := by
  -- The intersection of two open sets is open.
  have hOpen : IsOpen (A ∩ B : Set X) := hA.inter hB
  -- Any open set satisfies `P3`.
  exact Topology.open_satisfies_P3 (A := A ∩ B) hOpen

theorem all_Ps_iff_P3_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed (A : Set X)) :
    (Topology.P1 (A : Set X) ∧ Topology.P2 A ∧ Topology.P3 A) ↔ Topology.P3 A := by
  constructor
  · intro h
    exact h.2.2
  · intro hP3
    have hP1 : Topology.P1 (A : Set X) :=
      (Topology.P3_implies_P1_of_closed (A := A) hA) hP3
    have hP2 : Topology.P2 (A : Set X) :=
      (Topology.P3_implies_P2_of_closed (A := A) hA) hP3
    exact And.intro hP1 (And.intro hP2 hP3)

theorem closure_interior_eq_univ_of_dense_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) →
      closure (A : Set X) = (Set.univ : Set X) →
      closure (interior (A : Set X)) = (Set.univ : Set X) := by
  intro hP2 hDense
  -- From `P2`, we know the closures of `A` and `interior A` coincide.
  have hEq : closure (interior (A : Set X)) = closure A :=
    Topology.P2_implies_closure_interior_eq_closure (A := A) hP2
  -- Combine this with the density hypothesis.
  simpa [hDense] using hEq.trans hDense

theorem nonempty_iff_nonempty_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (A : Set X)) :
    A.Nonempty ↔ (interior (A : Set X)).Nonempty := by
  constructor
  · intro hA
    exact nonempty_interior_of_nonempty_P1 (A := A) hP1 hA
  · intro hInt
    rcases hInt with ⟨x, hxInt⟩
    exact ⟨x, (interior_subset : interior (A : Set X) ⊆ A) hxInt⟩

theorem interior_closure_subset_interior_closure_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A : Set X)) ⊆ interior (closure (A ∪ B)) := by
  -- First, note the basic inclusion `A ⊆ A ∪ B`.
  have hSub : (A : Set X) ⊆ A ∪ B := by
    intro x hx
    exact Or.inl hx
  -- Lift this inclusion through `closure`.
  have hClSub : closure (A : Set X) ⊆ closure (A ∪ B) :=
    closure_mono hSub
  -- Finally, apply monotonicity of `interior`.
  exact interior_mono hClSub

theorem interior_closure_empty {X : Type*} [TopologicalSpace X] :
    interior (closure (∅ : Set X)) = (∅ : Set X) := by
  simpa [closure_empty]

theorem closure_interior_iInter_subset_iInter_closure_interior
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {S : ι → Set X} :
    closure (interior (⋂ i, S i : Set X)) ⊆ ⋂ i, closure (interior (S i)) := by
  intro x hx
  have hForall : ∀ i, x ∈ closure (interior (S i)) := by
    intro i
    -- `interior (⋂ i, S i)` is contained in `interior (S i)`
    have hSub :
        interior (⋂ i, S i : Set X) ⊆ interior (S i) := by
      intro y hy
      have hyInter :
          y ∈ (⋂ i, interior (S i) : Set X) :=
        (interior_iInter_subset_iInter_interior (S := S)) hy
      exact (Set.mem_iInter.1 hyInter) i
    -- Taking closures preserves this inclusion
    have hClSub :
        closure (interior (⋂ i, S i : Set X))
          ⊆ closure (interior (S i)) :=
      closure_mono hSub
    exact hClSub hx
  exact Set.mem_iInter.2 hForall

theorem nonempty_iff_nonempty_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (A : Set X)) :
    (A : Set X).Nonempty ↔ (interior (A : Set X)).Nonempty := by
  constructor
  · intro hA
    exact nonempty_interior_of_nonempty_P2 (A := A) hP2 hA
  · intro hInt
    rcases hInt with ⟨x, hxInt⟩
    exact ⟨x, (interior_subset : interior (A : Set X) ⊆ A) hxInt⟩

theorem closure_interior_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (interior (closure (A : Set X)))) =
      closure (interior (closure A)) := by
  simpa [interior_interior]

theorem open_of_P3_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior (A : Set X))) → IsOpen (closure (interior A)) := by
  intro hP3
  simpa using (open_of_P3_closure (A := interior (A : Set X)) hP3)

theorem isClosed_union_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed (closure (interior (A : Set X)) ∪ closure (interior B)) := by
  have hA : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  have hB : IsClosed (closure (interior (B : Set X))) := isClosed_closure
  exact hA.union hB

theorem nonempty_iff_nonempty_interior_of_open
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    (A : Set X).Nonempty ↔ (interior (A : Set X)).Nonempty := by
  have hEq : interior (A : Set X) = A := hA.interior_eq
  constructor
  · intro hNon
    simpa [hEq] using hNon
  · intro hInt
    simpa [hEq] using hInt

theorem closure_union_of_closures {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (closure (A : Set X) ∪ closure B) = closure A ∪ closure B := by
  calc
    closure (closure (A : Set X) ∪ closure B)
        = closure (closure (A : Set X)) ∪ closure (closure B) := by
          simpa using closure_union (closure (A : Set X)) (closure B)
    _ = closure (A : Set X) ∪ closure B := by
          simpa [closure_closure]

theorem open_iff_all_Ps_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    IsOpen (A : Set X) ↔
      (Topology.P1 (A : Set X) ∧ Topology.P2 A ∧ Topology.P3 A) := by
  calc
    IsOpen (A : Set X) ↔ Topology.P2 A :=
      (Topology.P2_iff_open_of_closed (A := A) hClosed).symm
    _ ↔ (Topology.P1 (A : Set X) ∧ Topology.P2 A ∧ Topology.P3 A) :=
      (Topology.all_Ps_iff_P2_of_closed (A := A) hClosed).symm

theorem open_subset_closure_implies_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hOpenU : IsOpen (U : Set X)) (hSub : U ⊆ closure (A : Set X)) :
    U ⊆ interior (closure A) := by
  exact interior_maximal hSub hOpenU

theorem interior_closure_eq_self_of_P2_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) →
      interior (closure (A : Set X)) = closure A := by
  intro hP2
  -- From `P2` we know that `closure A` is open.
  have hOpen : IsOpen (closure (A : Set X)) :=
    Topology.open_of_P2_closure (A := A) hP2
  -- For an open set, its interior equals itself.
  simpa using hOpen.interior_eq

theorem interior_closure_univ {X : Type*} [TopologicalSpace X] :
    interior (closure (Set.univ : Set X)) = (Set.univ : Set X) := by
  simp [closure_univ, interior_univ]

theorem interior_closure_eq_univ_iff_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) = (Set.univ : Set X) ↔
      closure (A : Set X) = (Set.univ : Set X) := by
  constructor
  · intro hInt
    have hSub : (Set.univ : Set X) ⊆ closure (A : Set X) := by
      have hIntSub : interior (closure (A : Set X)) ⊆ closure A :=
        interior_subset
      simpa [hInt] using hIntSub
    have hSup : closure (A : Set X) ⊆ (Set.univ : Set X) :=
      Set.subset_univ _
    exact Set.Subset.antisymm hSup hSub
  · intro hClos
    simpa [hClos, interior_univ]

theorem open_iff_interior_eq_self {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (A : Set X) ↔ interior (A : Set X) = A := by
  constructor
  · intro hOpen
    simpa using hOpen.interior_eq
  · intro hEq
    have hOpenInt : IsOpen (interior (A : Set X)) := isOpen_interior
    simpa [hEq] using hOpenInt

theorem P1_inter_of_P1_and_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP1 : Topology.P1 (A : Set X)) (hOpenB : IsOpen (B : Set X)) :
    Topology.P1 (A ∩ B) := by
  -- Unfold the definition of `P1`.
  dsimp [Topology.P1] at hP1 ⊢
  intro x hxAB
  rcases hxAB with ⟨hxA, hxB⟩
  -- `x` lies in `closure (interior A)` thanks to `P1` for `A`.
  have hx_clA : x ∈ closure (interior (A : Set X)) := hP1 hxA
  -- We prove `x ∈ closure (interior (A ∩ B))` via the neighborhood
  -- characterization of the closure.
  apply (mem_closure_iff).2
  intro U hU hxU
  -- Intersect the given neighborhood with `B`, which is open and contains `x`.
  have hV_open : IsOpen (U ∩ B) := hU.inter hOpenB
  have hxV    : x ∈ U ∩ B       := And.intro hxU hxB
  -- Since `x ∈ closure (interior A)`, this new neighborhood meets `interior A`.
  have hNon : ((U ∩ B) ∩ interior (A : Set X)).Nonempty :=
    ((mem_closure_iff).1 hx_clA) (U ∩ B) hV_open hxV
  rcases hNon with ⟨y, ⟨hyU, hyB⟩, hyIntA⟩
  -- We will show that such a point `y` actually belongs to
  -- `interior (A ∩ B)` and, hence, to the required intersection.
  have hyIntAB : y ∈ interior (A ∩ B) := by
    -- `y` lies in `interior A ∩ B`.
    have hyIn : y ∈ (interior (A : Set X)) ∩ B := And.intro hyIntA hyB
    -- The set `interior A ∩ B` is open and contained in `A ∩ B`,
    -- so it sits inside `interior (A ∩ B)`.
    have hSub :
        ((interior (A : Set X)) ∩ B : Set X) ⊆ interior (A ∩ B) := by
      have hOpen : IsOpen ((interior (A : Set X)) ∩ B : Set X) :=
        (isOpen_interior).inter hOpenB
      have hIncl :
          ((interior (A : Set X)) ∩ B : Set X) ⊆ (A ∩ B) := by
        intro z hz
        exact And.intro
          ((interior_subset : interior (A : Set X) ⊆ A) hz.1) hz.2
      exact interior_maximal hIncl hOpen
    exact hSub hyIn
  -- Assemble the witness of non-emptiness required by `mem_closure_iff`.
  exact ⟨y, And.intro hyU hyIntAB⟩

theorem interior_iUnion_eq_iUnion_of_open {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {S : ι → Set X} (hS : ∀ i, IsOpen (S i)) :
    interior (⋃ i, S i : Set X) = ⋃ i, S i := by
  have hOpen : IsOpen (⋃ i, S i : Set X) := by
    simpa using isOpen_iUnion (fun i => hS i)
  simpa [hOpen.interior_eq]

theorem interior_closure_interior_eq_univ_iff_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (A : Set X))) = (Set.univ : Set X) ↔
      closure (interior (A : Set X)) = (Set.univ : Set X) := by
  constructor
  · intro hInt
    -- `interior s ⊆ s`, so the given equality forces
    -- `closure (interior A)` to cover the whole space.
    have hSub : (Set.univ : Set X) ⊆ closure (interior (A : Set X)) := by
      have hIncl :
          interior (closure (interior (A : Set X))) ⊆
            closure (interior (A : Set X)) :=
        interior_subset
      simpa [hInt] using hIncl
    -- The reverse inclusion is trivial.
    have hSup : closure (interior (A : Set X)) ⊆ (Set.univ : Set X) :=
      Set.subset_univ _
    exact Set.Subset.antisymm hSup hSub
  · intro hClos
    -- Rewriting with the hypothesis and `interior_univ`.
    have hEq :
        interior (closure (interior (A : Set X))) =
          interior (Set.univ : Set X) := by
      simpa [hClos]
    simpa [interior_univ] using hEq

theorem interior_closure_inter_closures_subset_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A : Set X)) ∩ closure B) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- `closure A ∩ closure B` sits inside each factor.
  have hSubA :
      closure ((A : Set X)) ∩ closure B ⊆ closure A := by
    intro y hy
    exact hy.1
  have hSubB :
      closure ((A : Set X)) ∩ closure B ⊆ closure B := by
    intro y hy
    exact hy.2
  -- Apply monotonicity of `interior` to obtain the two memberships.
  have hxA : x ∈ interior (closure A) :=
    (interior_mono hSubA) hx
  have hxB : x ∈ interior (closure B) :=
    (interior_mono hSubB) hx
  exact And.intro hxA hxB

theorem P3_closure_interior_iff_P2_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior (A : Set X))) ↔
      Topology.P2 (closure (interior A)) := by
  have h₁ :=
    (Topology.P3_closure_interior_iff_open_closure_interior
      (A := A))
  have h₂ :=
    (Topology.P2_closure_interior_iff_open_closure_interior
      (A := A))
  simpa using h₁.trans h₂.symm

theorem P2_closure_iff_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) ↔
      closure (A : Set X) ⊆ interior (closure A) := by
  have h₁ :=
    (Topology.P3_closure_iff_P2_closure (A := A)).symm
  have h₂ :=
    (Topology.P3_closure_iff_subset_interior_closure (A := A))
  exact h₁.trans h₂

theorem P3_closure_iff_interior_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) ↔
      interior (closure (A : Set X)) = closure A := by
  have h₁ := (Topology.P3_closure_iff_open_closure (A := A))
  have h₂ := (open_closure_iff_interior_eq_self (A := A))
  exact h₁.trans h₂

theorem interior_diff_eq_inter_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsClosed (B : Set X)) :
    interior ((A \ B) : Set X) = interior A \ B := by
  have hOpenComp : IsOpen (Bᶜ : Set X) := hB.isOpen_compl
  simpa [Set.diff_eq] using
    (interior_inter_of_isOpen_right (A := A) (B := Bᶜ) hOpenComp)

theorem interior_closure_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) ⊆ closure (interior (closure A)) := by
  simpa using
    (subset_closure :
      interior (closure (A : Set X)) ⊆ closure (interior (closure A)))

theorem P2_implies_P3_of_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P3 (interior A) := by
  intro _
  exact Topology.open_satisfies_P3 (A := interior A) isOpen_interior

theorem closure_interior_closure_interior_interior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (interior (A : Set X))))) =
      closure (interior A) := by
  simpa [interior_interior] using
    (closure_interior_closure_interior_eq (A := interior (A : Set X)))

theorem interior_iInter_closure_subset_iInter_interior_closure
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {S : ι → Set X} :
    interior (⋂ i, closure (S i) : Set X) ⊆ ⋂ i, interior (closure (S i)) := by
  intro x hx
  -- For each index `i`, we will show `x ∈ interior (closure (S i))`.
  have hx_i : ∀ i, x ∈ interior (closure (S i)) := by
    intro i
    -- The intersection is contained in each component `closure (S i)`.
    have hSub : (⋂ j, closure (S j) : Set X) ⊆ closure (S i) := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Monotonicity of `interior` upgrades the inclusion.
    exact (interior_mono hSub) hx
  -- Combine the pointwise facts into membership in the intersection.
  exact Set.mem_iInter.2 hx_i

theorem interior_closure_interior_closure_interior_closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior (closure (A : Set X)))))))) =
      interior (closure A) := by
  calc
    interior (closure (interior (closure (interior (closure (interior (closure A)))))))
        = interior (closure (interior (closure (interior (closure A))))) := by
          simpa using
            (interior_closure_interior_closure_eq
              (A := interior (closure (interior (closure A)))))
    _ = interior (closure (interior (closure A))) := by
          simpa using
            (interior_closure_interior_closure_eq
              (A := interior (closure A)))
    _ = interior (closure A) := by
          simpa using
            (interior_closure_interior_closure_eq (A := A))

theorem isClosed_of_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (A : Set X) = A) : IsClosed (A : Set X) := by
  simpa [h] using (isClosed_closure : IsClosed (closure (A : Set X)))

theorem nonempty_of_nonempty_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (A : Set X)).Nonempty → A.Nonempty := by
  rintro ⟨x, hxInt⟩
  exact ⟨x, (interior_subset : interior (A : Set X) ⊆ A) hxInt⟩

theorem interior_closure_subset_interior_closure_union_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (B : Set X)) ⊆ interior (closure (A ∪ B : Set X)) := by
  -- First, note the obvious inclusion `B ⊆ A ∪ B`.
  have hSub : (B : Set X) ⊆ A ∪ B := by
    intro x hx
    exact Or.inr hx
  -- Taking closures preserves inclusions.
  have hClSub : closure (B : Set X) ⊆ closure (A ∪ B) :=
    closure_mono hSub
  -- Finally, apply monotonicity of `interior`.
  exact interior_mono hClSub

theorem P1_inter_of_open_and_P1 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hOpenA : IsOpen (A : Set X)) (hP1B : Topology.P1 (B : Set X)) :
    Topology.P1 (A ∩ B) := by
  have h := Topology.P1_inter_of_P1_and_open (A := B) (B := A) hP1B hOpenA
  simpa [Set.inter_comm] using h

theorem closed_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (interior (A : Set X))) := by
  simpa using
    (isClosed_closure : IsClosed (closure (interior (A : Set X))))

theorem closure_iInter_eq_iInter_of_closed
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {S : ι → Set X}
    (hS : ∀ i, IsClosed (S i)) :
    closure (⋂ i, S i : Set X) = ⋂ i, S i := by
  have hClosed : IsClosed (⋂ i, S i : Set X) :=
    isClosed_iInter (fun i ↦ hS i)
  simpa [hClosed.closure_eq]

theorem closure_subset_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) → closure A ⊆ closure (interior A) := by
  intro hP1
  -- `P1` gives the inclusion `A ⊆ closure (interior A)`.
  have hSub : (A : Set X) ⊆ closure (interior A) := hP1
  -- Taking closures preserves inclusions.
  have hClos : closure (A : Set X) ⊆ closure (closure (interior A)) :=
    closure_mono hSub
  -- Simplify using idempotence of `closure`.
  simpa [closure_closure] using hClos

theorem interior_closure_interior_closure_interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior (closure (interior (A : Set X))))))))) =
      interior (closure (interior A)) := by
  calc
    interior (closure (interior (closure (interior (closure (interior (closure (interior (A : Set X))))))))) =
        interior (closure (interior (closure (interior (closure (interior (A : Set X))))))) := by
          simpa using
            (interior_closure_interior_closure_eq
              (A := interior (closure (interior (closure (interior (A : Set X)))))))
    _ = interior (closure (interior (closure (interior (A : Set X))))) := by
          simpa using
            (interior_closure_interior_closure_eq
              (A := interior (closure (interior (A : Set X)))))
    _ = interior (closure (interior (A : Set X))) := by
          simpa using
            (interior_closure_interior_closure_eq (A := A))

theorem P1_P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) → Topology.P2 A → Topology.P3 A := by
  intro _ hP2
  exact Topology.P2_implies_P3 (A := A) hP2

theorem closure_interior_eq_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) → closure (interior A) = closure A := by
  intro hP1
  exact (Topology.P1_iff_closure_interior_eq_closure (A := A)).1 hP1

theorem clopen_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (A : Set X)) (hClosed : IsClosed (A : Set X)) :
    Topology.P1 (A : Set X) ∧ Topology.P2 A ∧ Topology.P3 A := by
  simpa using Topology.open_satisfies_all_Ps (A := A) hOpen



theorem isClosed_inter_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed (closure (interior (A : Set X)) ∩ closure (interior B)) := by
  have hA : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  have hB : IsClosed (closure (interior (B : Set X))) := isClosed_closure
  exact hA.inter hB

theorem closure_eq_self_iff_closed {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = A ↔ IsClosed (A : Set X) := by
  constructor
  · intro h
    exact isClosed_of_closure_eq (A := A) h
  · intro hClosed
    simpa using hClosed.closure_eq

theorem P2_iff_P3_and_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) ↔
      (Topology.P3 A ∧
        interior (closure (A : Set X)) = interior (closure (interior A))) := by
  constructor
  · intro hP2
    have hP3 : Topology.P3 (A : Set X) :=
      Topology.P2_implies_P3 (A := A) hP2
    have hEq :
        interior (closure (A : Set X)) =
          interior (closure (interior A)) :=
      Topology.P2_implies_interior_closure_eq (A := A) hP2
    exact And.intro hP3 hEq
  · rintro ⟨hP3, hEq⟩
    exact
      Topology.P3_and_interiors_equal_implies_P2
        (A := A) hP3 hEq

theorem isClosed_union_closures
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed (closure (A : Set X) ∪ closure B) := by
  have hA : IsClosed (closure (A : Set X)) := isClosed_closure
  have hB : IsClosed (closure B) := isClosed_closure
  exact hA.union hB

theorem interior_union_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] (A B : Set X) :
    Topology.P1 (interior A ∪ interior B) ∧
      Topology.P2 (interior A ∪ interior B) ∧
      Topology.P3 (interior A ∪ interior B) := by
  -- The interiors of any sets are open.
  have hOpenA : IsOpen (interior A) := isOpen_interior
  have hOpenB : IsOpen (interior B) := isOpen_interior
  -- Apply the existing lemma for unions of open sets.
  simpa using
    (Topology.open_union_satisfies_all_Ps
      (A := interior A) (B := interior B) hOpenA hOpenB)

theorem union_interior_closure_and_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) ∪ closure (interior A) ⊆ closure A := by
  intro x hx
  cases hx with
  | inl hxInt =>
      exact (interior_subset : interior (closure (A : Set X)) ⊆ closure A) hxInt
  | inr hxCl =>
      -- `interior A ⊆ A`, so their closures satisfy the same inclusion.
      have hSub : interior (A : Set X) ⊆ A := interior_subset
      have hClSub : closure (interior (A : Set X)) ⊆ closure A :=
        closure_mono hSub
      exact hClSub hxCl

theorem closure_interior_closure_subset_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    closure (interior (closure (A : Set X))) ⊆ A := by
  -- Since `A` is closed, its closure is itself.
  have hEq : closure (A : Set X) = A := hA.closure_eq
  -- `interior (closure A)` is contained in `closure A`, hence in `A`.
  have hSub : interior (closure (A : Set X)) ⊆ A := by
    simpa [hEq] using
      (interior_subset : interior (closure (A : Set X)) ⊆ closure A)
  -- Taking closures preserves inclusions; rewrite using `hEq`.
  simpa [hEq, closure_closure] using (closure_mono hSub)

theorem open_of_closed_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X))
    (hDenseInt : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    IsOpen (A : Set X) := by
  -- The density assumption yields `P3` for the closed set `A`.
  have hP3 : Topology.P3 (A : Set X) :=
    Topology.dense_interior_satisfies_P3 (A := A) hDenseInt
  -- A closed set satisfying `P3` is necessarily open.
  exact (Topology.open_of_P3_closed (A := A) hClosed) hP3

theorem open_closure_inter {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (closure (A : Set X))) (hB : IsOpen (closure B)) :
    IsOpen (closure (A : Set X) ∩ closure B) := by
  simpa using (hA.inter hB)

theorem closure_inter_of_closures
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (closure (A : Set X) ∩ closure B) = closure A ∩ closure B := by
  -- The intersection of two closed sets is closed.
  have hClosed : IsClosed (closure (A : Set X) ∩ closure B) := by
    exact
      (isClosed_closure (s := (A : Set X))).inter
        (isClosed_closure (s := (B : Set X)))
  -- Taking the closure of a closed set leaves it unchanged.
  simpa [hClosed.closure_eq]





theorem P1_inter_of_P1_and_open_fixed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP1 : Topology.P1 (A : Set X)) (hOpenB : IsOpen (B : Set X)) :
    Topology.P1 (A ∩ B) := by
  -- Unpack the definition of `P1` for `A` and the goal.
  dsimp [Topology.P1] at hP1 ⊢
  intro x hxAB
  rcases hxAB with ⟨hxA, hxB⟩
  -- `x` lies in `closure (interior A)` thanks to `P1 A`.
  have hx_clA : x ∈ closure (interior (A : Set X)) := hP1 hxA
  -- We will prove that `x ∈ closure (interior (A ∩ B))`
  -- using the neighbourhood‐characterisation of the closure.
  have hx_cl : x ∈ closure (interior (A ∩ B)) := by
    -- Reformulate `closure` membership via `mem_closure_iff`.
    apply (mem_closure_iff).2
    intro U hU hxU
    -- Intersect the given neighbourhood with `B`, which is open and contains `x`.
    have hV_open : IsOpen (U ∩ B) := hU.inter hOpenB
    have hxV     : x ∈ U ∩ B       := And.intro hxU hxB
    -- Since `x ∈ closure (interior A)`, this new neighbourhood meets `interior A`.
    have hNon : ((U ∩ B) ∩ interior (A : Set X)).Nonempty :=
      (mem_closure_iff).1 hx_clA (U ∩ B) hV_open hxV
    -- Extract a witness `y`.
    rcases hNon with ⟨y, ⟨⟨hyU, hyB⟩, hyIntA⟩⟩
    -- `y` lies in `interior A ∩ B`, hence in `interior (A ∩ B)`
    -- because `B` is open.
    have hyIntAB : y ∈ interior (A ∩ B) := by
      have hEq :=
        (interior_inter_of_isOpen_right (A := A) (B := B) hOpenB)
      have : y ∈ interior A ∩ B := And.intro hyIntA hyB
      simpa [hEq] using this
    -- Provide the required witness inside `U ∩ interior (A ∩ B)`.
    exact ⟨y, And.intro hyU hyIntAB⟩
  -- Conclude the goal.
  exact hx_cl

theorem closure_interior_closure_subset_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    closure (interior (closure (A : Set X))) ⊆ A := by
  -- Since `A` is closed we have `closure A = A`.
  simpa [hA.closure_eq] using
    (closure_interior_subset_of_closed (A := A) hA)

theorem open_closure_interior_iff_all_Ps
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (interior (A : Set X))) ↔
      (Topology.P1 (closure (interior A)) ∧
        Topology.P2 (closure (interior A)) ∧
        Topology.P3 (closure (interior A))) := by
  constructor
  · intro hOpen
    simpa using
      (Topology.open_closure_interior_satisfies_all_Ps
        (A := A) hOpen)
  · rintro ⟨_, _, hP3⟩
    exact
      ((Topology.P3_closure_interior_iff_open_closure_interior
        (A := A)).1 hP3)

theorem closure_iUnion_closure_eq_closure_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} (S : ι → Set X) :
    closure (⋃ i, closure (S i) : Set X) = closure (⋃ i, S i) := by
  apply Set.Subset.antisymm
  · -- `⋃ i, closure (S i)` is contained in `closure (⋃ i, S i)`
    have hSub : (⋃ i, closure (S i) : Set X) ⊆ closure (⋃ i, S i) :=
      iUnion_closure_subset_closure_iUnion (S := S)
    -- Taking closures and simplifying yields the desired inclusion.
    simpa [closure_closure] using (closure_mono hSub)
  · -- Each `S i` is contained in `closure (S i)`, hence the unions satisfy the same.
    have hSub : (⋃ i, S i : Set X) ⊆ ⋃ i, closure (S i) := by
      intro x hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxSi⟩
      exact Set.mem_iUnion.2 ⟨i, (subset_closure hxSi)⟩
    -- Monotonicity of `closure` gives the reverse inclusion.
    simpa using (closure_mono hSub)

theorem Topology.subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    (A : Set X) ⊆ closure A := by
  intro x hxA
  -- Use the neighborhood characterization of `closure`.
  apply (mem_closure_iff).2
  intro U hU hxU
  exact ⟨x, And.intro hxU hxA⟩

theorem interior_closure_subset_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) →
      interior (closure (A : Set X)) ⊆ closure (interior A) := by
  intro hP2
  -- `P2` yields the equality of the two closures.
  have hEq : closure (interior (A : Set X)) = closure A :=
    Topology.P2_implies_closure_interior_eq_closure (A := A) hP2
  -- Hence their interiors coincide.
  have hIntEq :
      interior (closure (A : Set X)) = interior (closure (interior A)) := by
    simpa using congrArg interior hEq.symm
  -- Use the equality together with `interior_subset`.
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := by
    simpa [hIntEq] using hx
  exact (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx'

theorem interior_eq_univ_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) = (Set.univ : Set X) → Topology.P2 A := by
  intro hInt
  dsimp [Topology.P2]
  intro x _hxA
  have hIntCl :
      interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
    simpa [hInt, closure_univ, interior_univ]
  have hx : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hIntCl] using hx

theorem closure_inter_eq_inter_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed (A : Set X)) (hB : IsClosed (B : Set X)) :
    closure ((A ∩ B) : Set X) = A ∩ B := by
  -- The intersection of two closed sets is closed.
  have hClosed : IsClosed ((A ∩ B) : Set X) := hA.inter hB
  -- Taking the closure of a closed set leaves it unchanged.
  simpa using hClosed.closure_eq

theorem P2_inter_of_P2_and_open
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP2A : Topology.P2 (A : Set X)) (hOpenB : IsOpen (B : Set X)) :
    Topology.P2 (A ∩ B) := by
  -- Unfold `P2` for the given set and for the goal.
  dsimp [Topology.P2] at hP2A ⊢
  intro x hxAB
  rcases hxAB with ⟨hxA, hxB⟩
  -- From `P2` for `A`, place `x` in the required interior.
  have hxIntA : x ∈ interior (closure (interior A)) := hP2A hxA
  -- Define an auxiliary open neighbourhood of `x`.
  let V : Set X := interior (closure (interior A)) ∩ B
  have hV_open : IsOpen V := isOpen_interior.inter hOpenB
  have hxV    : x ∈ V := by
    dsimp [V]
    exact And.intro hxIntA hxB
  -- Show that this neighbourhood is contained in the desired closure.
  have hV_sub : (V : Set X) ⊆ closure (interior (A ∩ B)) := by
    intro y hyV
    rcases hyV with ⟨hyIntA, hyB⟩
    -- We prove `y ∈ closure (interior (A ∩ B))` via the neighbourhood
    -- characterisation of the closure.
    have hyClA : y ∈ closure (interior A) := by
      -- `interior S ⊆ S`
      exact (interior_subset : interior (closure (interior A)) ⊆
        closure (interior A)) hyIntA
    -- Reformulate the goal using `mem_closure_iff`.
    have : y ∈ closure (interior (A ∩ B)) := by
      -- Use `mem_closure_iff`.
      apply (mem_closure_iff).2
      intro U hU hyU
      -- Intersect the neighbourhood with `B`, which is open and contains `y`.
      have hU' : IsOpen (U ∩ B) := hU.inter hOpenB
      have hyU' : y ∈ U ∩ B := And.intro hyU hyB
      -- Since `y ∈ closure (interior A)`, this new neighbourhood meets `interior A`.
      have hNon : ((U ∩ B) ∩ interior (A : Set X)).Nonempty :=
        (mem_closure_iff).1 hyClA (U ∩ B) hU' hyU'
      rcases hNon with ⟨z, ⟨hzU, hzB⟩, hzIntA⟩
      -- `z` lies in `interior A ∩ B`, hence in `interior (A ∩ B)`
      -- because `B` is open.
      have hzIntAB : z ∈ interior (A ∩ B) := by
        -- `interior (A ∩ B) = interior A ∩ B` for an open `B`.
        have hEq :=
          interior_inter_of_isOpen_right (A := A) (B := B) hOpenB
        have hz : z ∈ interior A ∩ B := And.intro hzIntA hzB
        simpa [hEq] using hz
      -- Provide the witness required by `mem_closure_iff`.
      exact ⟨z, And.intro hzU hzIntAB⟩
    exact this
  -- Apply `interior_maximal` to conclude that `x` lies in the required interior.
  have hxGoal :
      x ∈ interior (closure (interior (A ∩ B))) :=
    (interior_maximal hV_sub hV_open) hxV
  exact hxGoal

theorem closure_interior_eq_self_of_clopen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (A : Set X)) (hClosed : IsClosed (A : Set X)) :
    closure (interior (A : Set X)) = A := by
  -- Since `A` is open, its interior is itself.
  have hInt : interior (A : Set X) = A := hOpen.interior_eq
  -- Taking closures and rewriting via `hInt`.
  have hClos : closure (interior (A : Set X)) = closure A := by
    simpa [hInt]
  -- As `A` is closed, its closure is itself.
  simpa [hClosed.closure_eq] using hClos

theorem nonempty_iff_nonempty_interior_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (A : Set X)) :
    (A : Set X).Nonempty ↔ (interior (closure (A : Set X))).Nonempty := by
  classical
  constructor
  · intro hA
    exact
      nonempty_interior_closure_of_nonempty_P3 (A := A) hP3 hA
  · intro hInt
    by_cases hA : (A : Set X).Nonempty
    · exact hA
    · exfalso
      -- From `¬ A.Nonempty`, deduce `interior (closure A)` is empty,
      -- contradicting `hInt`.
      have hIntEq :
          interior (closure (A : Set X)) = (∅ : Set X) := by
        have hAeq : (A : Set X) = ∅ := by
          simpa [Set.not_nonempty_iff_eq_empty] using hA
        simpa [hAeq, closure_empty, interior_empty]
      rcases hInt with ⟨x, hx⟩
      simpa [hIntEq] using hx

theorem P2_inter_of_open_and_P2
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hOpenA : IsOpen (A : Set X)) (hP2B : Topology.P2 (B : Set X)) :
    Topology.P2 (A ∩ B) := by
  -- Apply the existing lemma with the factors swapped, then rewrite.
  have h :=
    Topology.P2_inter_of_P2_and_open (A := B) (B := A) hP2B hOpenA
  simpa [Set.inter_comm] using h

theorem P3_inter_of_P3_and_open
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP3 : Topology.P3 (A : Set X)) (hOpenB : IsOpen (B : Set X)) :
    Topology.P3 (A ∩ B) := by
  -- Unfold the definition of `P3`.
  dsimp [Topology.P3] at hP3 ⊢
  intro x hxAB
  rcases hxAB with ⟨hxA, hxB⟩
  -- From `P3` for `A`, place `x` inside `interior (closure A)`.
  have hxIntA : x ∈ interior (closure (A : Set X)) := hP3 hxA
  -- Consider the open neighbourhood `V = interior (closure A) ∩ B` of `x`.
  let V : Set X := interior (closure (A : Set X)) ∩ B
  have hV_open : IsOpen V := isOpen_interior.inter hOpenB
  have hxV     : x ∈ V := by
    dsimp [V]
    exact And.intro hxIntA hxB
  -- We claim that `V ⊆ closure (A ∩ B)`.
  have hV_sub : (V : Set X) ⊆ closure (A ∩ B) := by
    intro y hyV
    rcases hyV with ⟨hyIntA, hyB⟩
    -- `y` lies in `closure A`.
    have hyClA : y ∈ closure (A : Set X) :=
      (interior_subset : interior (closure (A : Set X)) ⊆ closure A) hyIntA
    -- Show `y ∈ closure (A ∩ B)` using the neighbourhood criterion.
    have : y ∈ closure (A ∩ B : Set X) := by
      -- Reformulate with `mem_closure_iff`.
      apply (mem_closure_iff).2
      intro U hU hyU
      -- Intersect the given neighbourhood with `B`, which is open and contains `y`.
      have hU' : IsOpen (U ∩ B) := hU.inter hOpenB
      have hyU' : y ∈ U ∩ B := And.intro hyU hyB
      -- Since `y ∈ closure A`, this new neighbourhood meets `A`.
      have hNon : ((U ∩ B) ∩ A).Nonempty :=
        (mem_closure_iff).1 hyClA (U ∩ B) hU' hyU'
      -- Extract a witness in `U ∩ (A ∩ B)`.
      rcases hNon with ⟨z, ⟨hzU, hzB⟩, hzA⟩
      exact ⟨z, And.intro hzU (And.intro hzA hzB)⟩
    exact this
  -- Conclude that `x ∈ interior (closure (A ∩ B))`.
  exact (interior_maximal hV_sub hV_open) hxV