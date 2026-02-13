

theorem isOpen_subset_closureInterior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (X:=X) A := by
  dsimp [Topology.P1]
  intro x hx
  have h_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  exact subset_closure h_int

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X:=X) A → Topology.P1 (X:=X) A := by
  intro hP2
  dsimp [Topology.P1, Topology.P2] at hP2 ⊢
  intro x hx
  exact interior_subset (hP2 hx)

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X:=X) A → Topology.P3 (X:=X) A := by
  intro hP2
  dsimp [Topology.P2, Topology.P3] at hP2 ⊢
  intro x hx
  have hx₁ : x ∈ interior (closure (interior A)) := hP2 hx
  have h_subset : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  exact (interior_mono h_subset) hx₁

theorem isOpen_subset_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 (X:=X) A := by
  dsimp [Topology.P3]
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  have h_incl : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact h_incl hx_int

theorem isOpen_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P2 (X := X) A := by
  dsimp [Topology.P2]
  intro x hx
  have hx' : x ∈ interior (closure A) :=
    (Topology.isOpen_subset_interiorClosure (X:=X) (A:=A) hA) hx
  simpa [hA.interior_eq] using hx'

theorem Topology.isOpen_subset_closureInterior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (X:=X) A := by
  dsimp [Topology.P1]
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  exact subset_closure hx_int

theorem Topology.dense_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Dense A) : Topology.P3 (X:=X) A := by
  dsimp [Topology.P3]
  intro x _
  have h_cl : closure A = (Set.univ : Set X) := hA.closure_eq
  simpa [h_cl, interior_univ]

theorem Topology.interior_closure_interior_subset_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  intro x hx
  have h_subset : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  exact (interior_mono h_subset) hx

theorem Topology.P1_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 (X:=X) A ↔ Topology.P2 (X:=X) A := by
  refine ⟨fun _ => isOpen_implies_P2 (X:=X) (A:=A) hA, ?_⟩
  intro hP2
  exact Topology.P2_implies_P1 (X:=X) (A:=A) hP2

theorem Topology.P2_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P2 (X:=X) A ↔ Topology.P3 (X:=X) A := by
  dsimp [Topology.P2, Topology.P3]
  have h_eq : interior (closure (interior A)) = interior (closure A) := by
    simpa [hA.interior_eq]
  simpa [h_eq]

theorem Topology.P1_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 (X:=X) A ↔ Topology.P3 (X:=X) A := by
  have h12 : Topology.P1 (X:=X) A ↔ Topology.P2 (X:=X) A :=
    Topology.P1_iff_P2_of_isOpen (X:=X) (A:=A) hA
  have h23 : Topology.P2 (X:=X) A ↔ Topology.P3 (X:=X) A :=
    Topology.P2_iff_P3_of_isOpen (X:=X) (A:=A) hA
  exact h12.trans h23

theorem Topology.P1_iff_closure_eq_closureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (X := X) A ↔ closure (A : Set X) = closure (interior A) := by
  constructor
  · intro hP1
    have h₁ : closure (A : Set X) ⊆ closure (interior A) := by
      -- Take closure on both sides of the inclusion provided by hP1
      have := closure_mono hP1
      simpa using this
    have h₂ : closure (interior A) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset : interior A ⊆ A)
    exact Set.Subset.antisymm h₁ h₂
  · intro h_eq
    dsimp [Topology.P1]
    intro x hxA
    have : (x : X) ∈ closure (A : Set X) := subset_closure hxA
    simpa [h_eq] using this

theorem Topology.closed_P3_implies_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X:=X) A) :
    IsOpen (A : Set X) := by
  have h_closure : closure (A : Set X) = A := hA_closed.closure_eq
  have h_subset : (A : Set X) ⊆ interior A := by
    dsimp [Topology.P3] at hP3
    simpa [h_closure] using hP3
  have h_eq : interior A = A := by
    apply Set.Subset.antisymm
    · exact interior_subset
    · exact h_subset
  have : IsOpen (interior A) := isOpen_interior
  simpa [h_eq] using this

theorem Topology.interior_closure_interior_eq_interior_closure_of_isOpen {X : Type*}
    [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    interior (closure (interior A)) = interior (closure A) := by
  simpa [hA.interior_eq]

theorem Topology.interior_closure_interior_closure_eq_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure A))) = interior (closure A) := by
  apply Set.Subset.antisymm
  ·
    have h :
        interior (closure (interior (closure A))) ⊆ interior (closure (closure A)) :=
      Topology.interior_closure_interior_subset_interior_closure (X:=X) (A:=closure A)
    simpa [closure_closure] using h
  ·
    intro x hx
    have hx_inner : (x : X) ∈ interior (interior (closure A)) := by
      simpa [interior_interior] using hx
    have h_subset : interior (closure A) ⊆ closure (interior (closure A)) := by
      intro y hy
      exact subset_closure hy
    have h_inc :
        interior (interior (closure A)) ⊆ interior (closure (interior (closure A))) :=
      interior_mono h_subset
    exact h_inc hx_inner

theorem Topology.P1_implies_interior_closure_eq_interior_closureInterior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X:=X) A →
      interior (closure (A : Set X)) = interior (closure (interior A)) := by
  intro hP1
  have h_cl : closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closureInterior (X:=X) (A:=A)).1 hP1
  simpa [h_cl]

theorem Topology.interior_closure_interior_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (interior A)) ⊆ closure (A : Set X) := by
  intro x hx
  have hx' : x ∈ interior (closure A) :=
    (Topology.interior_closure_interior_subset_interior_closure (X:=X) (A:=A)) hx
  exact interior_subset hx'

theorem Topology.P2_implies_closure_eq_closureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 (X:=X) A → closure (A : Set X) = closure (interior A) := by
  intro hP2
  have hP1 : Topology.P1 (X:=X) A :=
    Topology.P2_implies_P1 (X:=X) (A:=A) hP2
  exact (Topology.P1_iff_closure_eq_closureInterior (X:=X) (A:=A)).1 hP1

theorem Topology.interior_closure_interior_closure_interior_eq_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior A)))) = interior (closure (interior A)) := by
  apply Set.Subset.antisymm
  ·
    have h :
        interior (closure (interior (closure (interior A)))) ⊆
          interior (closure (closure (interior A))) :=
      Topology.interior_closure_interior_subset_interior_closure
        (X := X) (A := closure (interior A))
    simpa [closure_closure] using h
  ·
    intro x hx
    have hx_inner : (x : X) ∈ interior (interior (closure (interior A))) := by
      simpa [interior_interior] using hx
    have h_subset :
        interior (closure (interior A)) ⊆ closure (interior (closure (interior A))) := by
      intro y hy
      exact subset_closure hy
    have h_inc :
        interior (interior (closure (interior A))) ⊆
          interior (closure (interior (closure (interior A)))) :=
      interior_mono h_subset
    exact h_inc hx_inner

theorem Topology.P3_implies_closure_eq_closureInteriorClosure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X:=X) A → closure (A : Set X) = closure (interior (closure A)) := by
  intro hP3
  apply Set.Subset.antisymm
  ·
    have : closure (A : Set X) ⊆ closure (interior (closure A)) :=
      closure_mono (hP3 : (A : Set X) ⊆ interior (closure A))
    simpa using this
  ·
    have : closure (interior (closure A)) ⊆ closure (closure (A : Set X)) :=
      closure_mono (interior_subset : interior (closure A) ⊆ closure A)
    simpa [closure_closure] using this

theorem Topology.P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P3 (X:=X) A ↔ IsOpen (A : Set X) := by
  constructor
  · intro hP3
    exact Topology.closed_P3_implies_isOpen (X:=X) (A:=A) hA_closed hP3
  · intro hA_open
    exact Topology.isOpen_subset_interiorClosure (X:=X) (A:=A) hA_open

theorem Topology.P2_implies_interior_closure_eq_interior_closureInterior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X:=X) A →
      interior (closure (A : Set X)) = interior (closure (interior A)) := by
  intro hP2
  have hP1 : Topology.P1 (X:=X) A :=
    Topology.P2_implies_P1 (X:=X) (A:=A) hP2
  exact (Topology.P1_implies_interior_closure_eq_interior_closureInterior
    (X:=X) (A:=A)) hP1

theorem Topology.P2_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P2 (X:=X) A ↔ IsOpen (A : Set X) := by
  constructor
  · intro hP2
    have hP3 : Topology.P3 (X:=X) A :=
      Topology.P2_implies_P3 (X:=X) (A:=A) hP2
    exact Topology.closed_P3_implies_isOpen (X:=X) (A:=A) hA_closed hP3
  · intro hA_open
    exact isOpen_implies_P2 (X:=X) (A:=A) hA_open

theorem Topology.P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (interior (A : Set X)) := by
  dsimp [Topology.P1]
  intro x hx
  simpa [interior_interior] using (subset_closure hx)

theorem Topology.P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (interior (A : Set X)) := by
  have h_open : IsOpen (interior (A : Set X)) := isOpen_interior
  exact isOpen_implies_P2 (X := X) (A := interior A) h_open

theorem Topology.P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (interior (A : Set X)) := by
  have h_open : IsOpen (interior (A : Set X)) := isOpen_interior
  exact Topology.isOpen_subset_interiorClosure (X := X) (A := interior A) h_open

theorem Topology.P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (X := X) (Set.univ : Set X) := by
  dsimp [Topology.P2]
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem Topology.interior_closure_closure_eq_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure (closure A)) = interior (closure A) := by
  simpa [closure_closure]

theorem Topology.interior_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (A : Set X) ⊆ interior (closure A) := by
  intro x hx
  exact (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hx

theorem Topology.closure_interior_closure_interior_eq_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply Set.Subset.antisymm
  ·
    have h_subset :
        interior (closure (interior A)) ⊆ closure (interior A) := by
      simpa using interior_subset
    have h_closure :
        closure (interior (closure (interior A))) ⊆
          closure (closure (interior A)) :=
      closure_mono h_subset
    simpa [closure_closure] using h_closure
  ·
    have h_open : IsOpen (interior A) := isOpen_interior
    have h_inner :
        (interior A : Set X) ⊆ interior (closure (interior A)) :=
      interior_maximal
        (subset_closure : (interior A : Set X) ⊆ closure (interior A)) h_open
    have h_closure :
        closure (interior A) ⊆ closure (interior (closure (interior A))) :=
      closure_mono h_inner
    exact h_closure

theorem Topology.P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X:=X) A ↔ (Topology.P1 (X:=X) A ∧ Topology.P3 (X:=X) A) := by
  constructor
  · intro hP2
    exact
      ⟨Topology.P2_implies_P1 (X:=X) (A:=A) hP2,
        Topology.P2_implies_P3 (X:=X) (A:=A) hP2⟩
  · rintro ⟨hP1, hP3⟩
    dsimp [Topology.P2]
    intro x hxA
    -- Using P3, place x in the interior of the closure of A
    have hx_closureA : x ∈ interior (closure A) := hP3 hxA
    -- Obtain equality of closures from P1
    have h_cl_eq : closure (A : Set X) = closure (interior A) :=
      (Topology.P1_iff_closure_eq_closureInterior (X:=X) (A:=A)).1 hP1
    -- Rewrite to reach the desired conclusion
    simpa [h_cl_eq] using hx_closureA

theorem Topology.P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (X:=X) (Set.univ : Set X) := by
  dsimp [Topology.P3]
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem Topology.P3_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (interior (closure (A : Set X))) := by
  have h_open : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  exact
    Topology.isOpen_subset_interiorClosure
      (X := X) (A := interior (closure (A : Set X))) h_open

theorem Topology.P1_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (X := X) (Set.univ : Set X) := by
  dsimp [Topology.P1]
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem Topology.P1_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (interior (closure (A : Set X))) := by
  dsimp [Topology.P1]
  intro x hx
  have : (x : X) ∈ closure (interior (closure (A : Set X))) :=
    subset_closure hx
  simpa [interior_interior] using this

theorem Topology.P1_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B) :
    Topology.P1 (X := X) (A ∪ B) := by
  dsimp [Topology.P1] at *
  intro x hx
  cases hx with
  | inl hxA =>
      -- Use P1 for A
      have hx_clA : x ∈ closure (interior A) := hA hxA
      -- Monotonicity of interior and closure under union
      have h_subset : interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      have h_cl_subset :
          closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_subset
      exact h_cl_subset hx_clA
  | inr hxB =>
      -- Use P1 for B
      have hx_clB : x ∈ closure (interior B) := hB hxB
      have h_subset : interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      have h_cl_subset :
          closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_subset
      exact h_cl_subset hx_clB

theorem Topology.P3_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 (X:=X) A) (hB : Topology.P3 (X:=X) B) :
    Topology.P3 (X:=X) (A ∪ B) := by
  dsimp [Topology.P3] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_intA : x ∈ interior (closure A) := hA hxA
      have h_subset : closure A ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      have h_interior_subset :
          interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_subset
      exact h_interior_subset hx_intA
  | inr hxB =>
      have hx_intB : x ∈ interior (closure B) := hB hxB
      have h_subset : closure B ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      have h_interior_subset :
          interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_subset
      exact h_interior_subset hx_intB

theorem Topology.P2_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 (X := X) A) (hB : Topology.P2 (X := X) B) :
    Topology.P2 (X := X) (A ∪ B) := by
  dsimp [Topology.P2] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' : x ∈ interior (closure (interior A)) := hA hxA
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono
          (interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B))
      have h_int_subset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono h_subset
      exact h_int_subset hxA'
  | inr hxB =>
      have hxB' : x ∈ interior (closure (interior B)) := hB hxB
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono
          (interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B))
      have h_int_subset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono h_subset
      exact h_int_subset hxB'

theorem Topology.P3_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) A → Topology.P1 (X := X) (closure (A : Set X)) := by
  intro hP3
  dsimp [Topology.P1] -- unfold the definition of P1
  intro x hx_clA
  -- We first show that `closure A ⊆ closure (interior (closure A))`
  have h_subset : (closure (A : Set X)) ⊆ closure (interior (closure A)) := by
    -- Step 1: `A ⊆ closure (interior (closure A))`
    have hA_subset : (A : Set X) ⊆ closure (interior (closure A)) := by
      intro y hyA
      have hy_int : y ∈ interior (closure A) := hP3 hyA
      exact subset_closure hy_int
    -- Step 2: take closures on both sides of the previous inclusion
    have h_closure_subset :
        closure (A : Set X) ⊆ closure (closure (interior (closure A))) :=
      closure_mono hA_subset
    simpa [closure_closure] using h_closure_subset
  exact h_subset hx_clA

theorem Topology.P3_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (closure (A : Set X)) ↔ IsOpen (closure (A : Set X)) := by
  have h_closed : IsClosed (closure (A : Set X)) := isClosed_closure
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := closure A) h_closed)

theorem Topology.P2_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (interior (closure (A : Set X))) := by
  have h_open : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  exact isOpen_implies_P2 (X := X) (A := interior (closure (A : Set X))) h_open

theorem Topology.closure_interior_closure_eq_closure_of_isOpen {X : Type*}
    [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    closure (interior (closure A)) = closure A := by
  apply Set.Subset.antisymm
  ·
    have h_subset : interior (closure A) ⊆ closure A :=
      interior_subset
    have h_closure : closure (interior (closure A)) ⊆ closure (closure A) :=
      closure_mono h_subset
    simpa [closure_closure] using h_closure
  ·
    have h_interior : (A : Set X) ⊆ interior (closure A) :=
      interior_maximal (subset_closure : (A : Set X) ⊆ closure A) hA
    have h_closure : closure (A : Set X) ⊆ closure (interior (closure A)) :=
      closure_mono h_interior
    simpa using h_closure

theorem Topology.P1_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (X := X) (∅ : Set X) := by
  dsimp [Topology.P1]
  intro x hx
  cases hx

theorem Topology.P2_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X:=X) A → Topology.P1 (X:=X) (closure (A : Set X)) := by
  intro hP2
  have hP3 : Topology.P3 (X:=X) A :=
    Topology.P2_implies_P3 (X:=X) (A:=A) hP2
  exact Topology.P3_implies_P1_closure (X:=X) (A:=A) hP3

theorem Topology.P1_interiorClosureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (interior (closure (interior (A : Set X)))) := by
  simpa using
    (Topology.P1_interior (X := X) (A := closure (interior A)))

theorem Topology.P2_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure (A : Set X)) ↔ IsOpen (closure (A : Set X)) := by
  have h_closed : IsClosed (closure (A : Set X)) := isClosed_closure
  simpa using
    (Topology.P2_iff_isOpen_of_isClosed (X := X) (A := closure A) h_closed)

theorem Topology.P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P3 (X := X) (∅ : Set X) := by
  dsimp [Topology.P3]
  intro x hx
  cases hx

theorem Topology.P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (X := X) (∅ : Set X) := by
  dsimp [Topology.P2]
  intro x hx
  cases hx

theorem Topology.P1_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) A → Topology.P1 (X := X) (closure (A : Set X)) := by
  intro hP1
  dsimp [Topology.P1] at hP1 ⊢
  intro x hx_closureA
  -- Step 1: from `hP1`, lift the inclusion to closures.
  have h_cl1 : closure (A : Set X) ⊆ closure (closure (interior A)) :=
    closure_mono hP1
  have hx₁ : x ∈ closure (closure (interior A)) := h_cl1 hx_closureA
  -- Simplify the double closure.
  have hx₂ : x ∈ closure (interior A) := by
    simpa [closure_closure] using hx₁
  -- Step 2: relate `closure (interior A)` to `closure (interior (closure A))`.
  have h_cl2 : closure (interior A) ⊆ closure (interior (closure A)) := by
    have h_int : interior A ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono h_int
  exact h_cl2 hx₂

theorem Topology.closure_interior_closure_interior_closure_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure A))))
      = closure (interior (closure A)) := by
  simpa
    [Topology.interior_closure_interior_closure_eq_interior_closure (X := X) (A := A)]

theorem Topology.P2_interiorClosureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (interior (closure (interior (A : Set X)))) := by
  have h_open : IsOpen (interior (closure (interior (A : Set X)))) := isOpen_interior
  exact isOpen_implies_P2 (X := X) (A := interior (closure (interior A))) h_open

theorem Topology.interior_closure_interior_subset_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior A) := by
  intro x hx
  exact
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx

theorem Topology.P3_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (closure (A : Set X)) → Topology.P3 (X := X) A := by
  intro hP3cl
  dsimp [Topology.P3] at *
  intro x hx
  -- First, place `x` inside `closure A`.
  have hx_cl : (x : X) ∈ closure (A : Set X) := subset_closure hx
  -- Apply the P3 hypothesis for `closure A`.
  have hx_int : (x : X) ∈ interior (closure (closure (A : Set X))) := hP3cl hx_cl
  -- Simplify the double closure.
  simpa [closure_closure] using hx_int

theorem Topology.P1_iff_closure_subset_closureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (X := X) A ↔ closure (A : Set X) ⊆ closure (interior A) := by
  constructor
  · intro hP1
    -- From `P1`, we have equality of the two closures, hence the desired subset.
    have h_eq : closure (A : Set X) = closure (interior A) :=
      (Topology.P1_iff_closure_eq_closureInterior (X := X) (A := A)).1 hP1
    simpa [h_eq]
  · intro h_subset
    -- The reverse inclusion always holds, giving equality of the closures.
    have h_subset' : closure (interior A) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset : interior A ⊆ A)
    have h_eq : closure (A : Set X) = closure (interior A) :=
      Set.Subset.antisymm h_subset h_subset'
    -- Convert the equality back to `P1`.
    exact
      (Topology.P1_iff_closure_eq_closureInterior (X := X) (A := A)).2 h_eq

theorem Topology.closed_P1_implies_closureInterior_eq_self {X : Type*}
    [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP1 : Topology.P1 (X:=X) A) :
    closure (interior A) = (A : Set X) := by
  -- From `P1` we have equality of closures of `A` and `interior A`
  have h_eq : closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closureInterior (X:=X) (A:=A)).1 hP1
  -- Use the closedness of `A` to rewrite `closure A` as `A`
  simpa [hA_closed.closure_eq] using h_eq.symm

theorem Topology.P1_closureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (closure (interior (A : Set X))) := by
  dsimp [Topology.P1]
  intro x hx
  -- First, we show that `interior A ⊆ interior (closure (interior A))`.
  have h_int_subset : interior (A : Set X) ⊆ interior (closure (interior A)) := by
    -- Use monotonicity of `interior` on the inclusion `interior A ⊆ closure (interior A)`.
    have h : (interior A : Set X) ⊆ closure (interior A) := subset_closure
    have : interior (interior A) ⊆ interior (closure (interior A)) :=
      interior_mono h
    simpa [interior_interior] using this
  -- Taking closures preserves the inclusion.
  have h_closure :
      closure (interior A) ⊆ closure (interior (closure (interior A))) :=
    closure_mono h_int_subset
  exact h_closure hx

theorem Topology.denseInterior_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P1 (X := X) A := by
  intro hDense
  dsimp [Topology.P1]
  intro x hxA
  have h_cl : closure (interior (A : Set X)) = (Set.univ : Set X) := hDense.closure_eq
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [h_cl] using this

theorem Topology.P1_iff_closureInterior_eq_self_of_isClosed {X : Type*}
    [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    Topology.P1 (X := X) A ↔ closure (interior A) = (A : Set X) := by
  -- Start from the general characterization of `P1`
  have h₁ :
      Topology.P1 (X := X) A ↔ closure (A : Set X) = closure (interior A) :=
    Topology.P1_iff_closure_eq_closureInterior (X := X) (A := A)
  -- Use the closedness of `A` to simplify `closure A`
  have h₂ :
      Topology.P1 (X := X) A ↔ (A : Set X) = closure (interior A) := by
    simpa [hA_closed.closure_eq] using h₁
  -- Re-express the equality in the desired order
  simpa [eq_comm] using h₂

theorem Topology.closure_eq_closureInterior_of_denseInterior {X : Type*}
    [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior (A : Set X))) :
    closure (A : Set X) = closure (interior A) := by
  have hP1 : Topology.P1 (X := X) A :=
    Topology.denseInterior_implies_P1 (X := X) (A := A) hDense
  exact
    (Topology.P1_iff_closure_eq_closureInterior (X := X) (A := A)).1 hP1

theorem Topology.interior_closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  intro x hx
  have h_closure_subset : closure (interior A) ⊆ closure (interior B) :=
    closure_mono (interior_mono hAB)
  exact (interior_mono h_closure_subset) hx

theorem Topology.closure_interior_closure_interior_closure_interior_closure_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior (closure A)))))) =
      closure (interior (closure A)) := by
  -- First, collapse the innermost five-layer expression using the existing lemma
  have h₁ :
      closure (interior (closure (interior (closure (interior (closure A)))))) =
        closure (interior (closure (interior (closure A)))) := by
    simpa using
      (Topology.closure_interior_closure_interior_closure_eq_closure_interior_closure
        (X := X) (A := interior (closure (A : Set X))))
  -- Next, collapse the resulting three-layer expression using the same lemma
  have h₂ :
      closure (interior (closure (interior (closure A)))) =
        closure (interior (closure A)) := by
    simpa using
      (Topology.closure_interior_closure_interior_closure_eq_closure_interior_closure
        (X := X) (A := A))
  -- Combine the two equalities
  calc
    closure (interior (closure (interior (closure (interior (closure A)))))) =
        closure (interior (closure (interior (closure A)))) := by
          simpa using h₁
    _ = closure (interior (closure A)) := by
          simpa using h₂

theorem Topology.closed_dense_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hA_dense : Dense (A : Set X)) :
    (A : Set X) = (Set.univ : Set X) := by
  -- The closure of a closed set is itself.
  have h_closure_closed : closure (A : Set X) = A := hA_closed.closure_eq
  -- The closure of a dense set is the whole space.
  have h_closure_dense : closure (A : Set X) = (Set.univ : Set X) := hA_dense.closure_eq
  -- Combine the two equalities.
  simpa [h_closure_closed] using h_closure_dense

theorem Topology.interior_closure_interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  calc
    interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) := by
          simpa using
            (Topology.interior_closure_interior_closure_interior_eq_interior_closure_interior
              (X := X) (A := closure A))
    _ = interior (closure A) := by
          simpa using
            (Topology.interior_closure_interior_closure_eq_interior_closure
              (X := X) (A := A))

theorem Topology.isOpen_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure (A : Set X))) :
    Topology.P3 (X:=X) A := by
  dsimp [Topology.P3]
  intro x hxA
  have hx_cl : (x : X) ∈ closure (A : Set X) := subset_closure hxA
  have h_eq : interior (closure (A : Set X)) = closure (A : Set X) :=
    h_open.interior_eq
  simpa [h_eq] using hx_cl

theorem Topology.P2_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure (A : Set X)) → Topology.P3 (X := X) A := by
  intro hP2cl
  -- From P2 for `closure A`, we obtain P3 for `closure A`.
  have hP3cl : Topology.P3 (X := X) (closure (A : Set X)) :=
    Topology.P2_implies_P3 (X := X) (A := closure A) hP2cl
  -- P3 for `closure A` implies P3 for `A`.
  exact Topology.P3_closure_implies_P3 (X := X) (A := A) hP3cl

theorem Topology.interior_closure_interior_closure_interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior (closure A))))))) =
      interior (closure A) := by
  -- Collapse the innermost three-layer expression.
  have h_inner :
      interior (closure (interior (closure (interior (closure A))))) =
        interior (closure A) := by
    simpa using
      (Topology.interior_closure_interior_closure_interior_closure_eq_interior_closure
        (X := X) (A := A))
  -- Rewrite the goal using `h_inner`, then finish with the two-layer lemma.
  calc
    interior (closure (interior (closure (interior (closure (interior (closure A))))))) =
        interior (closure (interior (closure A))) := by
          simpa [h_inner]
    _ = interior (closure A) := by
          simpa using
            (Topology.interior_closure_interior_closure_eq_interior_closure
              (X := X) (A := A))

theorem Topology.interior_interior_closure_eq_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (interior (closure (A : Set X))) = interior (closure A) := by
  simpa [interior_interior]

theorem Topology.isOpen_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_open : IsOpen (A : Set X)) :
    Topology.P1 (X := X) (closure (A : Set X)) := by
  dsimp [Topology.P1]
  intro x hx_closure
  have h_eq :
      closure (interior (closure (A : Set X))) = closure (A : Set X) :=
    Topology.closure_interior_closure_eq_closure_of_isOpen
      (X := X) (A := A) hA_open
  simpa [h_eq] using hx_closure

theorem Topology.P2_iff_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P2 (X:=X) A ↔ Topology.P3 (X:=X) A := by
  have hP2 : Topology.P2 (X:=X) A ↔ IsOpen (A : Set X) :=
    Topology.P2_iff_isOpen_of_isClosed (X:=X) (A:=A) hA_closed
  have hP3 : Topology.P3 (X:=X) A ↔ IsOpen (A : Set X) :=
    Topology.P3_iff_isOpen_of_isClosed (X:=X) (A:=A) hA_closed
  exact hP2.trans hP3.symm

theorem Topology.denseInterior_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P2 (X := X) A := by
  intro hDense
  dsimp [Topology.P2]
  intro x _
  simpa [hDense.closure_eq, interior_univ] using
    (by
      simp : (x : X) ∈ (Set.univ : Set X))

theorem Topology.closure_interior_closure_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    closure (interior (closure A)) ⊆ closure (interior (closure B)) := by
  -- First, enlarge `A` to `B` using closure monotonicity.
  have h_closure_subset : closure (A : Set X) ⊆ closure B := closure_mono hAB
  -- Then, apply interior monotonicity to the previous inclusion.
  have h_interior_subset :
      interior (closure (A : Set X)) ⊆ interior (closure B) :=
    interior_mono h_closure_subset
  -- Finally, take closures on both sides to obtain the desired inclusion.
  exact closure_mono h_interior_subset

theorem Topology.closed_P2_implies_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) (hP2 : Topology.P2 (X:=X) A) :
    interior (A : Set X) = A := by
  have hA_open : IsOpen (A : Set X) :=
    (Topology.P2_iff_isOpen_of_isClosed (X:=X) (A:=A) hA_closed).1 hP2
  simpa using hA_open.interior_eq

theorem Topology.interior_closure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    interior (closure (A : Set X)) ⊆ interior (closure B) := by
  intro x hx
  have h_closure : closure (A : Set X) ⊆ closure B := closure_mono hAB
  exact (interior_mono h_closure) hx

theorem Topology.closure_interior_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    closure (interior (A : Set X)) ⊆ closure (interior B) := by
  exact closure_mono (interior_mono hAB)

theorem Topology.isOpen_closure_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure (A : Set X))) :
    Topology.P2 (X:=X) (closure (A : Set X)) := by
  have h_equiv :
      Topology.P2 (X:=X) (closure (A : Set X)) ↔ IsOpen (closure (A : Set X)) :=
    Topology.P2_closure_iff_isOpen_closure (X:=X) (A:=A)
  exact (h_equiv.mpr h_open)

theorem Topology.interior_closure_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (A : Set X)) ⊆ closure A := by
  intro x hx
  exact (interior_subset : interior (closure (A : Set X)) ⊆ closure (A : Set X)) hx

theorem Set.Subset_univ {α : Type*} {s : Set α} : s ⊆ (Set.univ : Set α) := by
  intro x hx
  simp

theorem Topology.closure_interior_closure_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior (closure (A : Set X))) ⊆ closure A := by
  -- First, note that `interior (closure A)` is contained in `closure A`.
  have h_subset : interior (closure (A : Set X)) ⊆ closure A :=
    interior_subset
  -- Taking closures on both sides preserves the inclusion.
  have h_closure :
      closure (interior (closure (A : Set X))) ⊆ closure (closure A) :=
    closure_mono h_subset
  -- Simplify the right‐hand side using `closure_closure`.
  simpa [closure_closure] using h_closure

theorem Topology.isOpen_closure_implies_P1_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (h_open : IsOpen (closure (A : Set X))) :
    Topology.P1 (X := X) (closure (A : Set X)) := by
  -- Apply the generic P1 result for open sets to `closure A`.
  have hP1 :=
    isOpen_subset_closureInterior (X := X) (A := closure (A : Set X)) h_open
  simpa using hP1

theorem Topology.dense_implies_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_dense : Dense (A : Set X)) :
    Topology.P2 (X := X) (closure (A : Set X)) := by
  have h_closure_univ : closure (A : Set X) = (Set.univ : Set X) := hA_dense.closure_eq
  simpa [h_closure_univ] using (Topology.P2_univ (X := X))

theorem Topology.closure_interior_subset_closure_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) ⊆ closure (interior (closure A)) := by
  -- First, note that `A ⊆ closure A`.
  have h_subset : (A : Set X) ⊆ closure A := subset_closure
  -- Applying `interior` (which is monotone) to this inclusion yields
  -- `interior A ⊆ interior (closure A)`.
  have h_interior : interior (A : Set X) ⊆ interior (closure A) :=
    interior_mono h_subset
  -- Finally, taking `closure` (also monotone) on both sides gives the desired result.
  exact closure_mono h_interior

theorem Topology.closure_interior_inter_subset_inter_closure_interior {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (interior ((A ∩ B) : Set X)) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- `interior (A ∩ B)` is contained in both `interior A` and `interior B`
  have hA_subset : interior ((A ∩ B) : Set X) ⊆ interior A :=
    interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
  have hB_subset : interior ((A ∩ B) : Set X) ⊆ interior B :=
    interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
  -- Monotonicity of `closure` transports the point into the respective closures
  have hxA : x ∈ closure (interior A) := (closure_mono hA_subset) hx
  have hxB : x ∈ closure (interior B) := (closure_mono hB_subset) hx
  exact ⟨hxA, hxB⟩

theorem Topology.P3_inter_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X))
    (hPA : Topology.P3 (X:=X) A) (hPB : Topology.P3 (X:=X) B) :
    Topology.P3 (X:=X) (A ∩ B) := by
  -- Both sets are open because they are closed and satisfy P3
  have hA_open : IsOpen (A : Set X) :=
    Topology.closed_P3_implies_isOpen (X:=X) (A:=A) hA_closed hPA
  have hB_open : IsOpen (B : Set X) :=
    Topology.closed_P3_implies_isOpen (X:=X) (A:=B) hB_closed hPB
  -- The intersection of two open sets is open
  have h_inter_open : IsOpen ((A ∩ B) : Set X) := hA_open.inter hB_open
  -- Open sets always satisfy P3
  exact Topology.isOpen_subset_interiorClosure (X:=X) (A:=A ∩ B) h_inter_open

theorem Topology.dense_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_dense : Dense (A : Set X)) :
    Topology.P1 (X := X) (closure (A : Set X)) := by
  -- The closure of a dense set is the whole space.
  have h_closure : closure (A : Set X) = (Set.univ : Set X) := hA_dense.closure_eq
  -- P1 holds for the whole space.
  have hP1_univ : Topology.P1 (X := X) (Set.univ : Set X) :=
    Topology.P1_univ (X := X)
  -- Rewrite via `h_closure`.
  simpa [h_closure] using hP1_univ

theorem Topology.denseInterior_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P3 (X := X) A := by
  intro hDense
  dsimp [Topology.P3]
  intro x hxA
  -- First, show that `closure A = univ`.
  have h_univ_subset : (Set.univ : Set X) ⊆ closure (A : Set X) := by
    -- Since `interior A ⊆ A`, taking closures yields the inclusion we need.
    have h_subset : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset : interior (A : Set X) ⊆ A)
    -- Rewrite using the density of `interior A`.
    simpa [hDense.closure_eq] using h_subset
  have h_closureA_univ : closure (A : Set X) = (Set.univ : Set X) :=
    Set.Subset.antisymm Set.Subset_univ h_univ_subset
  -- Hence the interior of `closure A` is the whole space.
  have h_int_univ : interior (closure (A : Set X)) = (Set.univ : Set X) := by
    simpa [h_closureA_univ, interior_univ]
  -- The desired membership now follows.
  simpa [h_int_univ] using (by
    have : (x : X) ∈ (Set.univ : Set X) := by
      simp
    exact this)

theorem Topology.dense_implies_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_dense : Dense (A : Set X)) :
    Topology.P3 (X := X) (closure (A : Set X)) := by
  -- The closure of a dense set is the whole space.
  have h_closure : closure (A : Set X) = (Set.univ : Set X) := hA_dense.closure_eq
  -- `P3` holds for the whole space.
  have hP3_univ : Topology.P3 (X := X) (Set.univ : Set X) :=
    Topology.P3_univ (X := X)
  -- Rewrite using `h_closure`.
  simpa [h_closure] using hP3_univ

theorem Topology.interior_closure_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A : Set X)) ∪ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hA =>
      have h_subset : closure (A : Set X) ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      have h_int_subset :
          interior (closure (A : Set X)) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_subset
      exact h_int_subset hA
  | inr hB =>
      have h_subset : closure (B : Set X) ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      have h_int_subset :
          interior (closure (B : Set X)) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_subset
      exact h_int_subset hB

theorem Topology.closure_interior_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (A : Set X)) ∪ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `interior A ⊆ interior (A ∪ B)`
      have h_subset : interior (A : Set X) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      -- Taking closures preserves the inclusion
      have h_closure_subset :
          closure (interior (A : Set X)) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_subset
      exact h_closure_subset hxA
  | inr hxB =>
      -- `interior B ⊆ interior (A ∪ B)`
      have h_subset : interior (B : Set X) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      -- Taking closures preserves the inclusion
      have h_closure_subset :
          closure (interior (B : Set X)) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_subset
      exact h_closure_subset hxB

theorem Topology.interior_closure_inter_subset_inter_interior_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A ∩ B) : Set X)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- First, use monotonicity of `closure` and `interior` with respect to `A`.
  have hA_subset : closure ((A ∩ B) : Set X) ⊆ closure A :=
    closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
  have hxA : x ∈ interior (closure A) := (interior_mono hA_subset) hx
  -- Next, do the same with respect to `B`.
  have hB_subset : closure ((A ∩ B) : Set X) ⊆ closure B :=
    closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
  have hxB : x ∈ interior (closure B) := (interior_mono hB_subset) hx
  -- Combine the two inclusions to obtain the desired result.
  exact ⟨hxA, hxB⟩

theorem Topology.closure_interior_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior (A : Set X)) ⊆ closure A := by
  exact closure_mono (interior_subset : interior (A : Set X) ⊆ A)

theorem Topology.P1_inter_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P1 (X := X) (A ∩ B) := by
  have h_open : IsOpen ((A ∩ B) : Set X) := hA.inter hB
  exact isOpen_subset_closureInterior (X := X) (A := A ∩ B) h_open

theorem Topology.interior_closure_interior_eq_interior_of_isClosed {X : Type*}
    [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    interior (closure (interior A)) = interior A := by
  apply Set.Subset.antisymm
  · -- First inclusion: `interior (closure (interior A)) ⊆ interior A`.
    have h_subset : closure (interior A) ⊆ (A : Set X) := by
      -- `interior A ⊆ A`, hence their closures are related.
      have h_int : interior A ⊆ (A : Set X) := interior_subset
      have h_cl : closure (interior A) ⊆ closure (A : Set X) := closure_mono h_int
      simpa [hA_closed.closure_eq] using h_cl
    -- Monotonicity of `interior`.
    exact interior_mono h_subset
  · -- Second inclusion: `interior A ⊆ interior (closure (interior A))`.
    -- `interior A` is open and contained in `closure (interior A)`.
    have h_subset : (interior A : Set X) ⊆ closure (interior A) := subset_closure
    have h_open : IsOpen (interior A) := isOpen_interior
    exact interior_maximal h_subset h_open

theorem Topology.closed_dense_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hA_dense : Dense (A : Set X)) :
    IsOpen (A : Set X) := by
  have h_eq : (A : Set X) = (Set.univ : Set X) :=
    Topology.closed_dense_eq_univ (X := X) (A := A) hA_closed hA_dense
  simpa [h_eq] using isOpen_univ

theorem Topology.interior_closure_interior_closure_interior_closure_interior_closure_interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior (closure A))))))) =
      interior (closure A) := by
  -- First, collapse the innermost three‐layer expression.
  have h₁ :
      interior (closure (interior (closure (interior (closure A))))) =
        interior (closure A) := by
    simpa using
      (Topology.interior_closure_interior_closure_interior_closure_eq_interior_closure
        (X := X) (A := A))
  -- Second, recall the two‐layer idempotency of `interior ∘ closure`.
  have h₂ :
      interior (closure (interior (closure A))) = interior (closure A) := by
    simpa using
      (Topology.interior_closure_interior_closure_eq_interior_closure
        (X := X) (A := A))
  -- Combine the two simplifications to obtain the desired result.
  calc
    interior (closure (interior (closure (interior (closure (interior (closure A))))))) =
        interior (closure (interior (closure (interior (closure A))))) := by
          simpa [h₁]
    _ = interior (closure (interior (closure A))) := by
          simpa [h₁]
    _ = interior (closure A) := by
          simpa using h₂

theorem Topology.P2_closure_iff_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure (A : Set X)) ↔
      Topology.P3 (X := X) (closure (A : Set X)) := by
  -- Both properties are equivalent to `IsOpen (closure A)`.
  have hP2 := Topology.P2_closure_iff_isOpen_closure (X := X) (A := A)
  have hP3 := Topology.P3_closure_iff_isOpen_closure (X := X) (A := A)
  simpa using hP2.trans hP3.symm

theorem Topology.P2_inter_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P2 (X := X) (A ∩ B) := by
  have h_open : IsOpen ((A ∩ B) : Set X) := hA.inter hB
  exact isOpen_implies_P2 (X := X) (A := A ∩ B) h_open

theorem Topology.closed_dense_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hA_dense : Dense (A : Set X)) :
    Topology.P3 (X := X) A := by
  -- A closed and dense set is the whole space.
  have h_eq : (A : Set X) = (Set.univ : Set X) :=
    Topology.closed_dense_eq_univ (X := X) (A := A) hA_closed hA_dense
  -- `P3` holds for the whole space; rewrite via `h_eq`.
  simpa [h_eq] using Topology.P3_univ (X := X)

theorem Topology.P3_inter_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.P3 (X := X) (A ∩ B) := by
  -- The intersection of two open sets is open.
  have h_open : IsOpen ((A ∩ B) : Set X) := hA.inter hB
  -- Any open set satisfies `P3`.
  exact Topology.isOpen_subset_interiorClosure (X := X) (A := A ∩ B) h_open

theorem Topology.interior_closure_univ {X : Type*} [TopologicalSpace X] :
    interior (closure (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [closure_univ, interior_univ]

theorem Topology.dense_implies_closure_interior_closure_eq_univ {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) →
      closure (interior (closure (A : Set X))) = (Set.univ : Set X) := by
  intro hDense
  have h_cl : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  simpa [h_cl, interior_univ, closure_univ]

theorem Topology.dense_implies_interior_closure_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense (A : Set X) →
      interior (closure (A : Set X)) = (Set.univ : Set X) := by
  intro hDense
  have h_cl : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  simpa [h_cl, interior_univ]

theorem Topology.closureInterior_eq_closure_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen (A : Set X)) :
    closure (interior (A : Set X)) = closure (A : Set X) := by
  simpa [hA.interior_eq]

theorem Topology.P2_inter_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X))
    (hPA : Topology.P2 (X:=X) A) (hPB : Topology.P2 (X:=X) B) :
    Topology.P2 (X:=X) (A ∩ B) := by
  -- `A` is open because it is closed and satisfies `P2`
  have hA_open : IsOpen (A : Set X) := by
    have h_eq : interior (A : Set X) = A :=
      Topology.closed_P2_implies_interior_eq_self (X:=X) (A:=A) hA_closed hPA
    simpa [h_eq] using (isOpen_interior : IsOpen (interior (A : Set X)))
  -- `B` is open for the same reason
  have hB_open : IsOpen (B : Set X) := by
    have h_eq : interior (B : Set X) = B :=
      Topology.closed_P2_implies_interior_eq_self (X:=X) (A:=B) hB_closed hPB
    simpa [h_eq] using (isOpen_interior : IsOpen (interior (B : Set X)))
  -- The intersection of two open sets is open
  have h_open : IsOpen ((A ∩ B) : Set X) := hA_open.inter hB_open
  -- Any open set satisfies `P2`
  exact isOpen_implies_P2 (X:=X) (A:=A ∩ B) h_open

theorem Topology.closure_inter_subset_inter_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure ((A ∩ B) : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  have hxA : x ∈ closure A :=
    (closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx
  have hxB : x ∈ closure B :=
    (closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hx
  exact ⟨hxA, hxB⟩

theorem Topology.closed_P3_implies_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X:=X) A) :
    interior (A : Set X) = A := by
  have hA_open : IsOpen (A : Set X) :=
    Topology.closed_P3_implies_isOpen (X:=X) (A:=A) hA_closed hP3
  simpa using hA_open.interior_eq

theorem Topology.denseInterior_implies_closure_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense (interior (A : Set X)) →
      closure (A : Set X) = (Set.univ : Set X) := by
  intro hDense
  -- First, relate `closure A` to `closure (interior A)` using the existing lemma.
  have h_eq :
      closure (A : Set X) = closure (interior A) :=
    Topology.closure_eq_closureInterior_of_denseInterior (X := X) (A := A) hDense
  -- Since `interior A` is dense, its closure is the whole space.
  have h_closure_int : closure (interior A) = (Set.univ : Set X) := hDense.closure_eq
  -- Combine the two equalities.
  simpa [h_closure_int] using h_eq

theorem Topology.closed_dense_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hA_dense : Dense (A : Set X)) :
    Topology.P2 (X := X) A := by
  have hA_open : IsOpen (A : Set X) :=
    Topology.closed_dense_isOpen (X := X) (A := A) hA_closed hA_dense
  exact isOpen_implies_P2 (X := X) (A := A) hA_open

theorem Topology.isClosed_closureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (closure (interior (A : Set X))) := by
  simpa using
    (isClosed_closure : IsClosed (closure (interior (A : Set X))))

theorem Topology.closure_interior_interior_eq_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (interior (interior (A : Set X))) = closure (interior A) := by
  simpa [interior_interior]

theorem Topology.isOpen_implies_all_P {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    (Topology.P1 (X:=X) A) ∧ (Topology.P2 (X:=X) A) ∧ (Topology.P3 (X:=X) A) := by
  have hP1 := Topology.isOpen_subset_closureInterior (X := X) (A := A) hA
  have hP2 := isOpen_implies_P2 (X := X) (A := A) hA
  have hP3 := Topology.isOpen_subset_interiorClosure (X := X) (A := A) hA
  exact ⟨hP1, hP2, hP3⟩

theorem Topology.inter_closure_interior_subset_closure_interior_union {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X)) ∩ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  rcases hx with ⟨hA, _hB⟩
  -- `interior A` is contained in `interior (A ∪ B)`
  have h_subset : (interior (A : Set X)) ⊆ interior (A ∪ B) :=
    interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
  -- Taking closures preserves this inclusion
  have h_closure_subset :
      closure (interior (A : Set X)) ⊆ closure (interior (A ∪ B)) :=
    closure_mono h_subset
  exact h_closure_subset hA

theorem Topology.P3_implies_interior_closure_eq_interior_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X:=X) A →
      interior (closure (A : Set X)) =
        interior (closure (interior (closure A))) := by
  intro hP3
  apply Set.Subset.antisymm
  ·
    -- From `P3`, obtain an inclusion between the corresponding closures
    have h_closure :
        closure (A : Set X) ⊆ closure (interior (closure A)) :=
      closure_mono (hP3 : (A : Set X) ⊆ interior (closure A))
    -- Monotonicity of `interior` yields the desired inclusion
    exact interior_mono h_closure
  ·
    -- The reverse inclusion follows from an existing lemma with `A := closure A`
    have h :=
      Topology.interior_closure_interior_subset_interior_closure
        (X := X) (A := closure A)
    simpa [closure_closure] using h

theorem Topology.P1_and_emptyInterior_implies_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 (X:=X) A) (h_int : interior (A : Set X) = ∅) :
    (A : Set X) = ∅ := by
  -- `P1` tells us that every point of `A` lies in `closure (interior A)`.
  -- If `interior A` is empty, that closure is also empty, forcing `A` itself to be empty.
  have h_subset : (A : Set X) ⊆ (∅ : Set X) := by
    intro x hxA
    have : x ∈ closure (interior (A : Set X)) := hP1 hxA
    simpa [h_int, closure_empty] using this
  exact Set.Subset.antisymm h_subset (Set.empty_subset _)

theorem Topology.P1_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B) :
    Topology.P1 (X := X) (closure ((A ∪ B) : Set X)) := by
  -- First, `P1` holds for the union `A ∪ B`.
  have h_union : Topology.P1 (X := X) (A ∪ B) :=
    Topology.P1_union (X := X) (A := A) (B := B) hA hB
  -- Then, `P1` is inherited by the closure of any set that satisfies `P1`.
  exact Topology.P1_implies_P1_closure (X := X) (A := A ∪ B) h_union

theorem Topology.closureInterior_subset_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    closure (interior (A : Set X)) ⊆ A := by
  -- Start from the basic inclusion `interior A ⊆ A`.
  have h_subset : interior (A : Set X) ⊆ A := interior_subset
  -- Taking closures on both sides preserves the inclusion.
  have h_closure : closure (interior (A : Set X)) ⊆ closure A :=
    closure_mono h_subset
  -- Use the closedness of `A` to rewrite `closure A` as `A`.
  simpa [hA_closed.closure_eq] using h_closure

theorem Topology.P3_interiorClosureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (interior (closure (interior (A : Set X)))) := by
  -- The set `interior (closure (interior A))` is open.
  have h_open : IsOpen (interior (closure (interior (A : Set X)))) := isOpen_interior
  -- Any open set satisfies `P3`.
  exact
    Topology.isOpen_subset_interiorClosure
      (X := X) (A := interior (closure (interior (A : Set X)))) h_open

theorem Topology.interior_subset_closureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ closure (interior (A : Set X)) := by
  intro x hx
  exact subset_closure hx

theorem Topology.P2_implies_closure_eq_closureInteriorClosure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X:=X) A → closure (A : Set X) = closure (interior (closure A)) := by
  intro hP2
  have hP3 : Topology.P3 (X:=X) A :=
    Topology.P2_implies_P3 (X:=X) (A:=A) hP2
  exact Topology.P3_implies_closure_eq_closureInteriorClosure (X:=X) (A:=A) hP3

theorem Topology.interior_closure_subset_closureInterior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) ⊆ closure (interior (closure (A : Set X))) := by
  intro x hx
  exact subset_closure hx

theorem Topology.interior_closure_empty {X : Type*} [TopologicalSpace X] :
    interior (closure (∅ : Set X)) = (∅ : Set X) := by
  simp

theorem Topology.dense_of_P1_and_denseInterior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) (hDenseInt : Dense (interior (A : Set X))) :
    Dense (A : Set X) := by
  dsimp [Dense] at hDenseInt ⊢
  have h_eq : closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closureInterior (X := X) (A := A)).1 hP1
  simpa [h_eq] using hDenseInt

theorem Topology.closure_interior_union_subset_union_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (interior ((A ∪ B) : Set X)) ⊆
      closure (A : Set X) ∪ closure (B : Set X) := by
  -- `interior (A ∪ B)` is contained in `A ∪ B`
  have h_subset : interior ((A ∪ B) : Set X) ⊆ (A ∪ B) := interior_subset
  -- Taking closures preserves this inclusion
  have h_closure :
      closure (interior ((A ∪ B) : Set X)) ⊆ closure (A ∪ B) :=
    closure_mono h_subset
  -- Rewrite `closure (A ∪ B)` as `closure A ∪ closure B`
  simpa [closure_union] using h_closure

theorem Topology.P3_and_emptyInteriorClosure_implies_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 (X := X) A)
    (h_int : interior (closure (A : Set X)) = ∅) :
    (A : Set X) = ∅ := by
  -- From `P3`, every point of `A` lies in `interior (closure A)`.
  have h_subset : (A : Set X) ⊆ (∅ : Set X) := by
    intro x hxA
    have : x ∈ interior (closure (A : Set X)) := hP3 hxA
    simpa [h_int] using this
  -- Combine the derived inclusion with the trivial one in the other direction.
  exact Set.Subset.antisymm h_subset (Set.empty_subset _)

theorem Topology.closed_P2_implies_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP2 : Topology.P2 (X:=X) A) :
    IsOpen (A : Set X) := by
  -- From the closedness of `A` and `P2`, we know `interior A = A`.
  have h_eq : interior (A : Set X) = A :=
    Topology.closed_P2_implies_interior_eq_self (X := X) (A := A) hA_closed hP2
  -- Since `interior A` is open, the equality gives the desired result.
  have : IsOpen (interior (A : Set X)) := isOpen_interior
  simpa [h_eq] using this

theorem Topology.closure_interior_closure_univ {X : Type*} [TopologicalSpace X] :
    closure (interior (closure (Set.univ : Set X))) = (Set.univ : Set X) := by
  simp [closure_univ, interior_univ]

theorem Topology.interior_closure_subset_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    interior (closure (A : Set X)) ⊆ A := by
  -- First, we have the general inclusion into the closure of `A`.
  have h_subset : interior (closure (A : Set X)) ⊆ closure A :=
    Topology.interior_closure_subset_closure (X := X) (A := A)
  -- Since `A` is closed, `closure A = A`.
  simpa [hA_closed.closure_eq] using h_subset

theorem Topology.interior_subset_interior_closureInterior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ interior (closure (interior A)) := by
  -- Apply monotonicity of `interior` to the inclusion
  -- `interior A ⊆ closure (interior A)`.
  have h :
      interior (interior (A : Set X)) ⊆ interior (closure (interior A)) :=
    interior_mono (subset_closure : (interior (A : Set X)) ⊆ closure (interior A))
  simpa [interior_interior] using h

theorem Topology.interior_closure_eq_interior_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    interior (closure (A : Set X)) = interior A := by
  simpa [hA_closed.closure_eq]

theorem Topology.closure_interior_diff_subset_closure_interior {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (interior ((A \ B) : Set X)) ⊆ closure (interior A) := by
  intro x hx
  -- `A \ B` is contained in `A`
  have h_subset : ((A \ B) : Set X) ⊆ A := by
    intro y hy
    exact hy.1
  -- Monotonicity of `interior`
  have h_interior : interior ((A \ B) : Set X) ⊆ interior A :=
    interior_mono h_subset
  -- Monotonicity of `closure`
  have h_closure :
      closure (interior ((A \ B) : Set X)) ⊆ closure (interior A) :=
    closure_mono h_interior
  exact h_closure hx

theorem Topology.closure_interior_univ {X : Type*} [TopologicalSpace X] :
    closure (interior (Set.univ : Set X)) = (Set.univ : Set X) := by
  simp [interior_univ, closure_univ]

theorem Topology.closed_dense_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hA_dense : Dense (A : Set X)) :
    Topology.P1 (X := X) A := by
  -- A closed and dense set is the whole space.
  have h_eq : (A : Set X) = (Set.univ : Set X) :=
    Topology.closed_dense_eq_univ (X := X) (A := A) hA_closed hA_dense
  -- `P1` holds for the whole space; rewrite via `h_eq`.
  simpa [h_eq] using Topology.P1_univ (X := X)

theorem Topology.interior_subset_closureInteriorClosure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (A : Set X) ⊆ closure (interior (closure A)) := by
  intro x hx
  have hx' : (x : X) ∈ interior (closure A) :=
    (Topology.interior_subset_interior_closure (X := X) (A := A)) hx
  exact subset_closure hx'

theorem Topology.closed_P3_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X:=X) A) :
    Topology.P2 (X:=X) A := by
  have h_equiv := Topology.P2_iff_P3_of_isClosed (X:=X) (A:=A) hA_closed
  exact h_equiv.mpr hP3

theorem Topology.interior_inter_subset_interior_intersection {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    (interior (A : Set X) ∩ interior B) ⊆ interior (A ∩ B) := by
  -- Let `x` be in the left-hand set.
  intro x hx
  -- The set `interior A ∩ interior B` is open.
  have h_open : IsOpen ((interior (A : Set X)) ∩ interior B) :=
    (isOpen_interior : IsOpen (interior (A : Set X))).inter isOpen_interior
  -- Moreover, it is contained in `A ∩ B`.
  have h_subset :
      ((interior (A : Set X)) ∩ interior B : Set X) ⊆ A ∩ B := by
    intro y hy
    exact ⟨(interior_subset : interior (A : Set X) ⊆ A) hy.1,
           (interior_subset : interior B ⊆ B) hy.2⟩
  -- Since `x` belongs to an open subset of `A ∩ B`, it lies in `interior (A ∩ B)`.
  have : x ∈ interior (A ∩ B) :=
    (interior_maximal (s := A ∩ B) h_subset h_open) hx
  exact this

theorem Topology.interior_closure_diff_subset_interior_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A \ B) : Set X)) ⊆ interior (closure A) := by
  intro x hx
  -- First, note that `A \ B ⊆ A`.
  have h_subset : ((A \ B) : Set X) ⊆ A := by
    intro y hy
    exact hy.1
  -- Taking closures preserves this inclusion.
  have h_closure : closure ((A \ B) : Set X) ⊆ closure A :=
    closure_mono h_subset
  -- Finally, apply monotonicity of `interior`.
  exact (interior_mono h_closure) hx

theorem Topology.closed_P3_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X:=X) A) :
    Topology.P1 (X:=X) A := by
  -- From the closedness of `A` and `P3`, we know that `A` is open.
  have hA_open : IsOpen (A : Set X) :=
    Topology.closed_P3_implies_isOpen (X := X) (A := A) hA_closed hP3
  -- Every open set satisfies `P1`.
  exact Topology.isOpen_subset_closureInterior (X := X) (A := A) hA_open

theorem Topology.closureInterior_eq_self_of_isClopen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_open : IsOpen (A : Set X)) (hA_closed : IsClosed (A : Set X)) :
    closure (interior (A : Set X)) = A := by
  have h_int : interior (A : Set X) = A := hA_open.interior_eq
  have h_cl : closure (A : Set X) = A := hA_closed.closure_eq
  simpa [h_int, h_cl]

theorem Topology.P2_and_emptyInterior_implies_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 (X:=X) A)
    (h_int : interior (A : Set X) = ∅) :
    (A : Set X) = ∅ := by
  -- The right side of the `P2` inclusion is empty because `interior A` is empty.
  have h_empty : interior (closure (interior (A : Set X))) = (∅ : Set X) := by
    simpa [h_int, closure_empty, interior_empty]
  -- Hence every point of `A` lies in the empty set, so `A` is empty.
  have h_subset : (A : Set X) ⊆ (∅ : Set X) := by
    intro x hxA
    have : (x : X) ∈ interior (closure (interior (A : Set X))) := hP2 hxA
    simpa [h_empty] using this
  exact Set.Subset.antisymm h_subset (Set.empty_subset _)

theorem Topology.P3_closure_implies_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X:=X) (closure (A : Set X)) →
      Topology.P2 (X:=X) (closure (A : Set X)) := by
  intro hP3
  exact (Topology.P2_closure_iff_P3_closure (X:=X) (A:=A)).2 hP3

theorem Topology.closed_P2_iff_interior_eq_self {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P2 (X := X) A ↔ interior (A : Set X) = A := by
  constructor
  · intro hP2
    exact Topology.closed_P2_implies_interior_eq_self (X := X) (A := A) hA_closed hP2
  · intro h_int_eq
    -- `interior A = A` implies that `A` is open.
    have hA_open : IsOpen (A : Set X) := by
      have h_open_int : IsOpen (interior (A : Set X)) := isOpen_interior
      simpa [h_int_eq] using h_open_int
    -- Every open set satisfies `P2`.
    exact isOpen_implies_P2 (X := X) (A := A) hA_open

theorem Topology.closure_interior_subset_closure_interior_union {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X)) ⊆ closure (interior (A ∪ B)) := by
  -- `A` is contained in `A ∪ B`, so the same holds for their interiors.
  have h_subset : interior (A : Set X) ⊆ interior (A ∪ B) :=
    interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
  -- Taking closures preserves inclusions.
  exact closure_mono h_subset

theorem Topology.union_interior_subset_interior_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A : Set X) ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- `interior A` is contained in `interior (A ∪ B)` because `A ⊆ A ∪ B`.
      have h : interior (A : Set X) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact h hA
  | inr hB =>
      -- `interior B` is contained in `interior (A ∪ B)` because `B ⊆ A ∪ B`.
      have h : interior (B : Set X) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact h hB

theorem Topology.closure_inter_interior_closure_eq_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    (closure (A : Set X)) ∩ interior (closure A) = interior (closure A) := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    exact And.intro (interior_subset hx) hx

theorem Topology.interior_subset_interior_union_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A : Set X) ⊆ interior (A ∪ B) := by
  exact interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)

theorem Topology.all_P_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (X := X) (Set.univ : Set X) ∧
      Topology.P2 (X := X) (Set.univ : Set X) ∧
        Topology.P3 (X := X) (Set.univ : Set X) := by
  exact
    ⟨Topology.P1_univ (X := X), Topology.P2_univ (X := X),
      Topology.P3_univ (X := X)⟩

theorem Topology.P1_inter_left_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hPA : Topology.P1 (X:=X) A) (hB_open : IsOpen (B : Set X)) :
    Topology.P1 (X:=X) (A ∩ B) := by
  dsimp [Topology.P1] at hPA ⊢
  intro x hx
  -- `x` belongs to both `A` and `B`.
  have hA : (x : X) ∈ A := hx.1
  have hB : (x : X) ∈ B := hx.2
  -- From `P1` for `A`, we know that `x` is in the closure of `interior A`.
  have hx_clA : x ∈ closure (interior A) := hPA hA
  -- We prove that `x` lies in the closure of `interior (A ∩ B)`.
  have hx_clAB : x ∈ closure (interior (A ∩ B)) := by
    -- Use the neighbourhood characterization of closure.
    apply (mem_closure_iff).2
    intro U hU hxU
    -- Consider the open neighbourhood `U ∩ B` of `x`.
    have hUB_open : IsOpen (U ∩ B) := hU.inter hB_open
    have hx_UB : (x : X) ∈ U ∩ B := ⟨hxU, hB⟩
    -- Apply the characterization of `hx_clA` with the neighbourhood `U ∩ B`.
    have h_nonempty : ((U ∩ B) ∩ interior A).Nonempty := by
      have h_prop := (mem_closure_iff).1 hx_clA
      have := h_prop (U ∩ B) hUB_open hx_UB
      -- Rearrange intersections to match Lean’s expectations.
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using this
    -- Extract a witness showing that `U` meets `interior (A ∩ B)`.
    rcases h_nonempty with ⟨y, ⟨⟨hyU, hyB⟩, hy_intA⟩⟩
    -- Since `B` is open, `interior B = B`.
    have hy_intB : y ∈ interior B := by
      simpa [hB_open.interior_eq] using hyB
    -- `interior (A ∩ B) = interior A ∩ interior B`.
    have h_int_eq : interior (A ∩ B) = interior A ∩ interior B := by
      simpa [Set.inter_comm] using interior_inter (A := A) (B := B)
    have hy_intAB : y ∈ interior (A ∩ B) := by
      have : y ∈ interior A ∩ interior B := ⟨hy_intA, hy_intB⟩
      simpa [h_int_eq] using this
    -- The required intersection with `U` is non‐empty.
    exact ⟨y, ⟨hyU, hy_intAB⟩⟩
  simpa using hx_clAB

theorem Topology.closure_inter_eq_of_closed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X)) :
    closure ((A ∩ B) : Set X) = A ∩ B := by
  have h_closed : IsClosed ((A ∩ B) : Set X) := hA_closed.inter hB_closed
  simpa using h_closed.closure_eq

theorem Topology.interior_inter_open_right {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB_open : IsOpen (B : Set X)) :
    interior ((A ∩ B) : Set X) = interior A ∩ B := by
  calc
    interior ((A ∩ B) : Set X)
        = interior A ∩ interior B := by
          simpa using interior_inter (A := A) (B := B)
    _ = interior A ∩ B := by
          simpa [hB_open.interior_eq]

theorem Topology.closure_interior_closure_interior_closure_subset_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (A : Set X))))) ⊆
      closure A := by
  -- First, reduce to `closure (interior (closure A))`.
  have h₁ :
      closure (interior (closure (interior (closure (A : Set X))))) ⊆
        closure (interior (closure (A : Set X))) :=
    Topology.closure_interior_closure_subset_closure
      (X := X) (A := interior (closure (A : Set X)))
  -- Then, relate this to `closure A`.
  have h₂ :
      closure (interior (closure (A : Set X))) ⊆ closure A :=
    Topology.closure_interior_closure_subset_closure (X := X) (A := A)
  exact Set.Subset.trans h₁ h₂

theorem Topology.denseInterior_implies_P1_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hDense : Dense (interior (A : Set X))) :
    Topology.P1 (X := X) (closure (A : Set X)) := by
  -- First, `P1` holds for `A` because the interior of `A` is dense.
  have hP1A : Topology.P1 (X := X) A :=
    Topology.denseInterior_implies_P1 (X := X) (A := A) hDense
  -- `P1` is inherited by the closure of any set that satisfies `P1`.
  exact Topology.P1_implies_P1_closure (X := X) (A := A) hP1A

theorem Topology.P1_closureInteriorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (closure (interior (closure (A : Set X)))) := by
  dsimp [Topology.P1]
  intro x hx
  -- `interior (closure (interior (closure A)))` simplifies to `interior (closure A)`
  -- via an existing lemma; hence their closures coincide.
  have h_int_eq :
      interior (closure (interior (closure (A : Set X)))) =
        interior (closure (A : Set X)) := by
    simpa using
      (Topology.interior_closure_interior_closure_eq_interior_closure
        (X := X) (A := A))
  -- Rewrite the target set using `h_int_eq` and conclude with `hx`.
  simpa [h_int_eq] using hx

theorem Topology.P3_closure_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (closure (A : Set X)) →
      Topology.P1 (X := X) (closure (A : Set X)) := by
  intro hP3cl
  -- From `P3` we infer that `closure A` is open, using the established equivalence.
  have h_open : IsOpen (closure (A : Set X)) :=
    ((Topology.P3_closure_iff_isOpen_closure (X := X) (A := A)).1) hP3cl
  -- Every open set satisfies `P1`.
  simpa using
    (Topology.isOpen_subset_closureInterior
      (X := X) (A := closure (A : Set X)) h_open)

theorem Topology.denseInterior_implies_interior_closure_interior_eq_univ {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) →
      interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
  intro hDense
  have h_closure : closure (interior (A : Set X)) = (Set.univ : Set X) :=
    hDense.closure_eq
  simpa [h_closure, interior_univ]

theorem Topology.P1_inter_right_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen (A : Set X)) (hPB : Topology.P1 (X:=X) B) :
    Topology.P1 (X:=X) (A ∩ B) := by
  -- Use commutativity of `∩` and the existing lemma `P1_inter_left_of_open`.
  have h := Topology.P1_inter_left_of_open (X:=X) (A:=B) (B:=A) hPB hA_open
  simpa [Set.inter_comm] using h

theorem Topology.interior_inter_open_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA_open : IsOpen (A : Set X)) :
    interior ((A ∩ B) : Set X) = A ∩ interior B := by
  calc
    interior ((A ∩ B) : Set X) = interior A ∩ interior B := by
      simpa using interior_inter (A := A) (B := B)
    _ = A ∩ interior B := by
      simpa [hA_open.interior_eq]

theorem Topology.P3_iff_interior_eq_self_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    Topology.P3 (X:=X) A ↔ interior (A : Set X) = A := by
  -- First, translate `P3` into the openness of `A` using the existing equivalence.
  have h₁ : Topology.P3 (X:=X) A ↔ IsOpen (A : Set X) :=
    Topology.P3_iff_isOpen_of_isClosed (X:=X) (A:=A) hA_closed
  -- Next, characterize openness via equality with the interior.
  have h₂ : IsOpen (A : Set X) ↔ interior (A : Set X) = A := by
    constructor
    · intro h_open
      simpa [h_open.interior_eq]
    · intro h_eq
      have h_open_int : IsOpen (interior (A : Set X)) := isOpen_interior
      simpa [h_eq] using h_open_int
  -- Combine the two equivalences.
  exact h₁.trans h₂

theorem Topology.P2_inter_left_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen (A : Set X)) (hPB : Topology.P2 (X := X) B) :
    Topology.P2 (X := X) (A ∩ B) := by
  -- Unfold the definition of `P2`.
  dsimp [Topology.P2] at hPB ⊢
  intro x hxAB
  -- Split the membership in the intersection.
  have hxA : (x : X) ∈ A := hxAB.1
  have hxB : (x : X) ∈ B := hxAB.2
  -- Use `P2` for `B` to place `x` in an appropriate interior.
  have hx_int : (x : X) ∈ interior (closure (interior B)) := hPB hxB
  -- Define the auxiliary open neighbourhood
  --   U = A ∩ interior (closure (interior B)).
  have hU_open : IsOpen (A ∩ interior (closure (interior B))) :=
    hA_open.inter isOpen_interior
  have hxU : (x : X) ∈ (A ∩ interior (closure (interior B))) :=
    ⟨hxA, hx_int⟩
  ------------------------------------------------------------------
  --  Step 1:  Show `U ⊆ closure (interior (A ∩ B))`.
  ------------------------------------------------------------------
  -- First enlarge `U` to `A ∩ closure (interior B)`.
  have h_step1 :
      (A ∩ interior (closure (interior B)) : Set X) ⊆
        A ∩ closure (interior B) := by
    intro y hy
    exact ⟨hy.1, interior_subset hy.2⟩
  -- Next show `A ∩ closure (interior B) ⊆ closure (interior (A ∩ B))`.
  have h_step2 :
      (A ∩ closure (interior B) : Set X) ⊆
        closure (interior (A ∩ B)) := by
    intro y hy
    have hyA  : (y : X) ∈ A := hy.1
    have hyCl : (y : X) ∈ closure (interior B) := hy.2
    ----------------------------------------------------------------
    --  Use the neighbourhood characterisation of closure.
    ----------------------------------------------------------------
    have hy_in_cl : (y : X) ∈ closure (A ∩ interior B) := by
      -- Characterisation of closure.
      apply (mem_closure_iff).2
      intro U hUopen hyU
      -- Consider `U ∩ A`, an open neighbourhood of `y`.
      have hUA_open : IsOpen (U ∩ A) := hUopen.inter hA_open
      have hyUA     : (y : X) ∈ U ∩ A := ⟨hyU, hyA⟩
      -- Since `y ∈ closure (interior B)`, the set `U ∩ A` meets `interior B`.
      have h_nonempty :
          ((U ∩ A) ∩ interior B : Set X).Nonempty := by
        have h_prop := (mem_closure_iff).1 hyCl
        have := h_prop (U ∩ A) hUA_open hyUA
        simpa [Set.inter_left_comm, Set.inter_assoc] using this
      rcases h_nonempty with ⟨z, ⟨⟨hzU, hzA⟩, hz_intB⟩⟩
      -- Exhibit the required point in `U ∩ (A ∩ interior B)`.
      exact ⟨z, ⟨hzU, hzA, hz_intB⟩⟩
    -- Rewrite using `interior (A ∩ B) = A ∩ interior B`
    -- (valid because `A` is open).
    have h_int_eq :
        interior (A ∩ B : Set X) = A ∩ interior B :=
      (Topology.interior_inter_open_left (X := X) (A := A) (B := B) hA_open)
    -- Convert `hy_in_cl` to the desired form.
    have : (y : X) ∈ closure (interior (A ∩ B)) := by
      simpa [h_int_eq] using hy_in_cl
    exact this
  -- Combine the two inclusions obtained so far.
  have h_subset :
      (A ∩ interior (closure (interior B)) : Set X) ⊆
        closure (interior (A ∩ B)) :=
    Set.Subset.trans h_step1 h_step2
  ------------------------------------------------------------------
  --  Step 2: Use `interior_maximal` to place `x` in the required interior.
  ------------------------------------------------------------------
  have h_into_interior :
      (A ∩ interior (closure (interior B)) : Set X) ⊆
        interior (closure (interior (A ∩ B))) :=
    interior_maximal h_subset hU_open
  exact h_into_interior hxU

theorem Topology.P1_interiorClosureSet {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (interior (closure (A : Set X))) := by
  -- The set `interior (closure A)` is open.
  have h_open : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  -- Any open set satisfies `P1`.
  exact
    Topology.isOpen_subset_closureInterior
      (X := X) (A := interior (closure (A : Set X))) h_open

theorem Topology.closed_P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP2 : Topology.P2 (X:=X) A) :
    Topology.P1 (X:=X) A := by
  have hA_open : IsOpen (A : Set X) :=
    Topology.closed_P2_implies_isOpen (X:=X) (A:=A) hA_closed hP2
  exact Topology.isOpen_subset_closureInterior (X:=X) (A:=A) hA_open

theorem Topology.interior_inter_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior ((A ∩ B) : Set X) = A ∩ B := by
  have h_open : IsOpen ((A ∩ B) : Set X) := hA.inter hB
  simpa using h_open.interior_eq

theorem Topology.closure_interior_empty {X : Type*} [TopologicalSpace X] :
    closure (interior (∅ : Set X)) = (∅ : Set X) := by
  simp

theorem Topology.interior_closure_union_subset_union_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A ∪ B) : Set X)) ⊆
      closure (A : Set X) ∪ closure B := by
  intro x hx
  have hx' : (x : X) ∈ closure ((A ∪ B) : Set X) := interior_subset hx
  simpa [closure_union] using hx'

theorem Topology.P2_inter_right_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hPA : Topology.P2 (X := X) A) (hB_open : IsOpen (B : Set X)) :
    Topology.P2 (X := X) (A ∩ B) := by
  -- Apply the “left” version with the roles of `A` and `B` swapped,
  -- then rewrite using commutativity of `∩`.
  have h :=
    Topology.P2_inter_left_of_open (X := X) (A := B) (B := A) hB_open hPA
  simpa [Set.inter_comm] using h

theorem Topology.closed_denseInterior_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (h_denseInt : Dense (interior (A : Set X))) :
    (A : Set X) = (Set.univ : Set X) := by
  -- From the density of `interior A`, we know that `closure A = univ`.
  have h_closure_univ :
      closure (A : Set X) = (Set.univ : Set X) :=
    Topology.denseInterior_implies_closure_eq_univ (X := X) (A := A) h_denseInt
  -- Since `A` is closed, its closure is itself.
  simpa [hA_closed.closure_eq] using h_closure_univ

theorem Topology.interior_union_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen (A : Set X)) (hB_open : IsOpen (B : Set X)) :
    interior ((A ∪ B) : Set X) = A ∪ B := by
  have h_open : IsOpen ((A ∪ B) : Set X) := hA_open.union hB_open
  simpa [h_open.interior_eq]

theorem Topology.closure_union_eq_of_closed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X)) :
    closure ((A ∪ B) : Set X) = (A ∪ B) := by
  have h_closed : IsClosed ((A ∪ B) : Set X) := hA_closed.union hB_closed
  simpa using h_closed.closure_eq

theorem Topology.interior_closure_eq_self_of_isClopen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_open : IsOpen (A : Set X)) (hA_closed : IsClosed (A : Set X)) :
    interior (closure (A : Set X)) = A := by
  -- First, use the closedness of `A` to simplify `interior (closure A)`.
  have h₁ : interior (closure (A : Set X)) = interior A :=
    Topology.interior_closure_eq_interior_of_isClosed (X := X) (A := A) hA_closed
  -- Next, use the openness of `A` to identify `interior A` with `A` itself.
  have h₂ : interior (A : Set X) = A := hA_open.interior_eq
  -- Combine the two equalities.
  simpa [h₂] using h₁

theorem Topology.interior_closure_interior_inter_subset_inter_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior ((A ∩ B) : Set X))) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  -- First direction: relate to `A`.
  have h_subsetA :
      closure (interior ((A ∩ B) : Set X)) ⊆ closure (interior A) := by
    have h_intA :
        interior ((A ∩ B) : Set X) ⊆ interior A :=
      interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
    exact closure_mono h_intA
  have hxA : x ∈ interior (closure (interior A)) :=
    (interior_mono h_subsetA) hx
  -- Second direction: relate to `B`.
  have h_subsetB :
      closure (interior ((A ∩ B) : Set X)) ⊆ closure (interior B) := by
    have h_intB :
        interior ((A ∩ B) : Set X) ⊆ interior B :=
      interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
    exact closure_mono h_intB
  have hxB : x ∈ interior (closure (interior B)) :=
    (interior_mono h_subsetB) hx
  exact ⟨hxA, hxB⟩

theorem Topology.interior_intersection_subset_inter_interior {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    interior ((A ∩ B) : Set X) ⊆ interior A ∩ interior B := by
  intro x hx
  -- `A ∩ B ⊆ A`, hence `interior (A ∩ B) ⊆ interior A`.
  have hxA : (x : X) ∈ interior A :=
    (interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx
  -- Similarly, `A ∩ B ⊆ B`, so `interior (A ∩ B) ⊆ interior B`.
  have hxB : (x : X) ∈ interior B :=
    (interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hx
  exact ⟨hxA, hxB⟩

theorem Topology.dense_iff_interior_closure_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense (A : Set X) ↔ interior (closure (A : Set X)) = (Set.univ : Set X) := by
  constructor
  · intro hDense
    exact Topology.dense_implies_interior_closure_eq_univ (X := X) (A := A) hDense
  · intro hInt
    -- From the assumption we first show `closure A = univ`.
    have hClosure : closure (A : Set X) = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · exact Set.subset_univ _
      · -- Since `interior (closure A)` equals `univ`, and `interior (closure A) ⊆ closure A`,
        -- the inclusion `univ ⊆ closure A` follows.
        have : interior (closure (A : Set X)) ⊆ closure (A : Set X) :=
          interior_subset
        simpa [hInt] using this
    -- Rewriting `Dense` shows the desired result.
    simpa [Dense, hClosure] using hClosure

theorem Topology.closure_interior_closure_interior_closure_interior_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior A))))) =
      closure (interior A) := by
  have h :
      closure (interior (closure (interior (closure (interior A))))) =
        closure (interior (interior A)) := by
    simpa using
      (Topology.closure_interior_closure_interior_closure_eq_closure_interior
        (X := X) (A := interior A))
  simpa [interior_interior] using h

theorem Topology.P3_inter_left_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen (A : Set X)) (hPB : Topology.P3 (X := X) B) :
    Topology.P3 (X := X) (A ∩ B) := by
  -- Unfold `P3` for `B`.
  dsimp [Topology.P3] at hPB ⊢
  intro x hxAB
  -- Split the membership in the intersection.
  have hxA : (x : X) ∈ A := hxAB.1
  have hxB : (x : X) ∈ B := hxAB.2
  -- Use `P3` for `B` to obtain an interior point.
  have hx_int_clB : (x : X) ∈ interior (closure B) := hPB hxB
  ------------------------------------------------------------------
  --  Construct an open neighbourhood `U := A ∩ interior (closure B)`
  --  that is contained in `closure (A ∩ B)`.
  ------------------------------------------------------------------
  have hU_open : IsOpen (A ∩ interior (closure B)) :=
    hA_open.inter isOpen_interior
  have hxU : (x : X) ∈ (A ∩ interior (closure B)) := ⟨hxA, hx_int_clB⟩
  -- `U` is contained in `closure (A ∩ B)`.
  have hU_subset : (A ∩ interior (closure B) : Set X) ⊆ closure (A ∩ B) := by
    intro y hy
    -- Separate the conditions on `y`.
    have hAy : (y : X) ∈ A := hy.1
    have hy_int : (y : X) ∈ interior (closure B) := hy.2
    -- Hence `y ∈ closure B`.
    have hClB : (y : X) ∈ closure B := interior_subset hy_int
    -- Show `y ∈ closure (A ∩ B)` via the neighbourhood characterization.
    have : (y : X) ∈ closure (A ∩ B) := by
      apply (mem_closure_iff).2
      intro U hUopen hyU
      -- Consider the open neighbourhood `U ∩ A` of `y`.
      have hUA_open : IsOpen (U ∩ A) := hUopen.inter hA_open
      have hyUA : (y : X) ∈ U ∩ A := ⟨hyU, hAy⟩
      -- Since `y ∈ closure B`, this set meets `B`.
      have h_nonempty :
          ((U ∩ A) ∩ B : Set X).Nonempty := by
        have h_prop := (mem_closure_iff).1 hClB
        have := h_prop (U ∩ A) hUA_open hyUA
        simpa [Set.inter_left_comm, Set.inter_assoc] using this
      -- Extract a witness in `U ∩ (A ∩ B)`.
      rcases h_nonempty with ⟨z, ⟨⟨hzU, hzA⟩, hzB⟩⟩
      exact ⟨z, ⟨hzU, ⟨hzA, hzB⟩⟩⟩
    exact this
  ------------------------------------------------------------------
  --  Apply `interior_maximal` to conclude.
  ------------------------------------------------------------------
  have h_into_int :
      (A ∩ interior (closure B) : Set X) ⊆ interior (closure (A ∩ B)) :=
    interior_maximal hU_subset hU_open
  exact h_into_int hxU

theorem Topology.interior_inter_closure_subset_closure_inter {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ∩ closure (B : Set X) ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hx_intA, hx_clB⟩
  -- We prove that `x` belongs to the closure of `A ∩ B`.
  have : (x : X) ∈ closure (A ∩ B) := by
    -- Use the neighbourhood characterization of the closure.
    apply (mem_closure_iff).2
    intro U hU_open hxU
    -- Consider the open neighbourhood `U ∩ interior A` of `x`.
    have hV_open : IsOpen (U ∩ interior (A : Set X)) :=
      hU_open.inter isOpen_interior
    have hxV : (x : X) ∈ U ∩ interior (A : Set X) := ⟨hxU, hx_intA⟩
    -- Since `x ∈ closure B`, this set meets `B`.
    have h_nonempty :
        ((U ∩ interior (A : Set X)) ∩ B : Set X).Nonempty := by
      have h_prop := (mem_closure_iff).1 hx_clB
      exact h_prop (U ∩ interior (A : Set X)) hV_open hxV
    -- Extract a witness and show it lies in `U ∩ (A ∩ B)`.
    rcases h_nonempty with ⟨y, ⟨⟨hyU, hy_intA⟩, hyB⟩⟩
    have hyA : (y : X) ∈ A := interior_subset hy_intA
    exact ⟨y, ⟨hyU, ⟨hyA, hyB⟩⟩⟩
  exact this

theorem Topology.denseInterior_implies_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P2 (X := X) (closure (A : Set X)) := by
  intro hDense
  have h_closure : closure (A : Set X) = (Set.univ : Set X) :=
    Topology.denseInterior_implies_closure_eq_univ (X := X) (A := A) hDense
  simpa [h_closure] using Topology.P2_univ (X := X)

theorem Topology.P3_inter_right_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hPA : Topology.P3 (X := X) A) (hB_open : IsOpen (B : Set X)) :
    Topology.P3 (X := X) (A ∩ B) := by
  -- Apply the “left” version with the roles of `A` and `B` swapped,
  -- then rewrite using commutativity of `∩`.
  have h :=
    Topology.P3_inter_left_of_open (X := X) (A := B) (B := A) hB_open hPA
  simpa [Set.inter_comm] using h

theorem Topology.interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ∪ interior B ⊆ interior (A ∪ B) := by
  simpa using
    (Topology.union_interior_subset_interior_union (X := X) (A := A) (B := B))

theorem Topology.closureInterior_eq_empty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) = (∅ : Set X) ↔ interior (A : Set X) = (∅ : Set X) := by
  constructor
  · intro h
    -- `interior A` is contained in its closure, which is empty by assumption.
    have h_subset : (interior (A : Set X)) ⊆ (∅ : Set X) := by
      intro x hx
      have : (x : X) ∈ closure (interior (A : Set X)) :=
        subset_closure hx
      simpa [h] using this
    exact Set.Subset.antisymm h_subset (Set.empty_subset _)
  · intro h_int
    simpa [h_int, closure_empty]

theorem Topology.interior_diff_closure_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A : Set X) \ closure (B : Set X) ⊆ interior (A \ B) := by
  rintro x ⟨hx_intA, hx_notClB⟩
  -- `interior A` is open.
  have h_open_intA : IsOpen (interior (A : Set X)) := isOpen_interior
  -- The complement of `closure B` is open as well.
  have h_open_compl : IsOpen ((closure (B : Set X))ᶜ) :=
    (isClosed_closure : IsClosed (closure (B : Set X))).isOpen_compl
  ------------------------------------------------------------------
  --  Construct an open neighbourhood of `x` contained in `A \ B`.
  ------------------------------------------------------------------
  let U := interior (A : Set X) ∩ (closure (B : Set X))ᶜ
  have hU_open : IsOpen U := h_open_intA.inter h_open_compl
  have hxU : (x : X) ∈ U := ⟨hx_intA, by
    -- `x ∉ closure B` gives membership in the complement.
    simpa using hx_notClB⟩
  -- Show that `U ⊆ A \ B`.
  have hU_subset : (U : Set X) ⊆ A \ B := by
    intro y hy
    have hA : (y : X) ∈ A :=
      (interior_subset : interior (A : Set X) ⊆ A) hy.1
    have h_notB : (y : X) ∉ B := by
      intro hyB
      have : (y : X) ∈ closure (B : Set X) := subset_closure hyB
      exact hy.2 this
    exact ⟨hA, h_notB⟩
  ------------------------------------------------------------------
  --  Conclude that `x` is in `interior (A \ B)`.
  ------------------------------------------------------------------
  exact
    (interior_maximal hU_subset hU_open) hxU

theorem Topology.interior_closure_interior_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (interior (A : Set X))) ∪ interior (closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- `A ⊆ A ∪ B`
      have h_subset : interior (A : Set X) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      -- Taking closures preserves the inclusion.
      have h_closure : closure (interior (A : Set X)) ⊆
          closure (interior (A ∪ B)) :=
        closure_mono h_subset
      -- Apply monotonicity of `interior`.
      exact (interior_mono h_closure) hA
  | inr hB =>
      -- `B ⊆ A ∪ B`
      have h_subset : interior (B : Set X) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      -- Taking closures preserves the inclusion.
      have h_closure : closure (interior (B : Set X)) ⊆
          closure (interior (A ∪ B)) :=
        closure_mono h_subset
      -- Apply monotonicity of `interior`.
      exact (interior_mono h_closure) hB

theorem Topology.P2_closure_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure (A : Set X)) →
      Topology.P1 (X := X) (closure (A : Set X)) := by
  intro hP2cl
  exact
    Topology.P2_implies_P1
      (X := X) (A := closure (A : Set X)) hP2cl

theorem Topology.interior_subset_interior_union_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (B : Set X) ⊆ interior (A ∪ B) := by
  simpa [Set.union_comm] using
    (Topology.interior_subset_interior_union_left (X := X) (A := B) (B := A))

theorem Topology.dense_implies_all_P_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (A : Set X)) :
    (Topology.P1 (X := X) (closure (A : Set X))) ∧
      (Topology.P2 (X := X) (closure (A : Set X))) ∧
        (Topology.P3 (X := X) (closure (A : Set X))) := by
  have hP1 := Topology.dense_implies_P1_closure (X := X) (A := A) hDense
  have hP2 := Topology.dense_implies_P2_closure (X := X) (A := A) hDense
  have hP3 := Topology.dense_implies_P3_closure (X := X) (A := A) hDense
  exact ⟨hP1, hP2, hP3⟩

theorem Topology.P1_closure_iff_closure_eq_closureInteriorClosure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (closure (A : Set X)) ↔
      closure (A : Set X) = closure (interior (closure A)) := by
  -- Apply the general characterization of `P1` with `A := closure A`
  have h :
      Topology.P1 (X := X) (closure (A : Set X)) ↔
        closure (closure (A : Set X)) = closure (interior (closure (A : Set X))) :=
    Topology.P1_iff_closure_eq_closureInterior (X := X) (A := closure A)
  -- Simplify both occurrences of `closure (closure A)`
  simpa [closure_closure] using h

theorem Topology.closure_inter_interior_subset_closure_inter {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) ∩ interior B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hx_clA, hx_intB⟩
  -- We prove that `x` belongs to the closure of `A ∩ B`.
  have : (x : X) ∈ closure (A ∩ B) := by
    -- Neighbourhood characterisation of the closure.
    apply (mem_closure_iff).2
    intro U hU_open hxU
    -- Consider the open neighbourhood `U ∩ interior B` of `x`.
    have hV_open : IsOpen (U ∩ interior B) := hU_open.inter isOpen_interior
    have hxV : (x : X) ∈ U ∩ interior B := ⟨hxU, hx_intB⟩
    -- Since `x ∈ closure A`, this set meets `A`.
    have h_nonempty :
        ((U ∩ interior B) ∩ A : Set X).Nonempty := by
      have h_prop := (mem_closure_iff).1 hx_clA
      have h := h_prop (U ∩ interior B) hV_open hxV
      simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using h
    -- Extract a witness in `U ∩ (A ∩ B)`.
    rcases h_nonempty with ⟨y, ⟨⟨hyU, hy_intB⟩, hyA⟩⟩
    have hyB : (y : X) ∈ B := interior_subset hy_intB
    exact ⟨y, ⟨hyU, ⟨hyA, hyB⟩⟩⟩
  exact this

theorem Topology.dense_of_P2_and_denseInterior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) (hDenseInt : Dense (interior (A : Set X))) :
    Dense (A : Set X) := by
  -- From `P2` we get `P1`.
  have hP1 : Topology.P1 (X := X) A :=
    Topology.P2_implies_P1 (X := X) (A := A) hP2
  -- Use the existing lemma that combines `P1` with density of `interior A`.
  exact
    Topology.dense_of_P1_and_denseInterior
      (X := X) (A := A) hP1 hDenseInt

theorem Topology.P1_and_P3_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) A → Topology.P3 (X := X) A → Topology.P2 (X := X) A := by
  intro hP1 hP3
  have h_equiv := Topology.P2_iff_P1_and_P3 (X := X) (A := A)
  exact (h_equiv.mpr ⟨hP1, hP3⟩)

theorem Topology.interior_closure_iterate_seven_eq_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure
      (interior (closure
        (interior (closure
          (interior (closure
            (interior (closure
              (interior (closure
                (interior (closure (A : Set X))))
              ))
            ))
          ))
        ))
      )) =
      interior (closure A) := by
  -- Repeatedly simplify using the idempotency of `interior ∘ closure`.
  simp [Topology.interior_closure_interior_closure_eq_interior_closure (X := X)]

theorem Topology.interior_closure_interior_closure_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (A : Set X)))) ⊆
      closure (interior (closure (A : Set X))) := by
  intro x hx
  exact
    (interior_subset :
      interior (closure (interior (closure (A : Set X)))) ⊆
        closure (interior (closure (A : Set X)))) hx

theorem Topology.P1_union_right_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hPA : Topology.P1 (X:=X) A) (hB_open : IsOpen (B : Set X)) :
    Topology.P1 (X:=X) (A ∪ B) := by
  -- An open set automatically satisfies `P1`.
  have hPB : Topology.P1 (X:=X) B :=
    Topology.isOpen_subset_closureInterior (X:=X) (A:=B) hB_open
  -- Combine the two `P1` properties via the existing union lemma.
  exact Topology.P1_union (X:=X) (A:=A) (B:=B) hPA hPB

theorem Topology.P2_union_right_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hPA : Topology.P2 (X := X) A) (hB_open : IsOpen (B : Set X)) :
    Topology.P2 (X := X) (A ∪ B) := by
  -- `B` is open, hence it satisfies `P2`.
  have hPB : Topology.P2 (X := X) B :=
    (isOpen_implies_P2 (X := X) (A := B) hB_open)
  -- Combine the two `P2` hypotheses using the existing union lemma.
  exact Topology.P2_union (X := X) (A := A) (B := B) hPA hPB

theorem Topology.P2_implies_closureInteriorClosureInterior_eq_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X:=X) A →
      closure (interior (closure (interior (A : Set X)))) = closure (A : Set X) := by
  intro hP2
  -- First, collapse the nested `closure ∘ interior` expression.
  have h₁ :
      closure (interior (closure (interior (A : Set X)))) =
        closure (interior A) :=
    Topology.closure_interior_closure_interior_eq_closure_interior (X := X) (A := A)
  -- Next, identify `closure (interior A)` with `closure A` using `P2`.
  have h₂ :
      closure (A : Set X) = closure (interior A) :=
    Topology.P2_implies_closure_eq_closureInterior (X := X) (A := A) hP2
  -- Combine the two equalities.
  simpa [h₂] using h₁

theorem Topology.denseInterior_implies_all_P {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense (interior (A : Set X)) →
      (Topology.P1 (X:=X) A) ∧
        (Topology.P2 (X:=X) A) ∧
          (Topology.P3 (X:=X) A) := by
  intro hDense
  have hP1 := Topology.denseInterior_implies_P1 (X := X) (A := A) hDense
  have hP2 := Topology.denseInterior_implies_P2 (X := X) (A := A) hDense
  have hP3 := Topology.denseInterior_implies_P3 (X := X) (A := A) hDense
  exact ⟨hP1, hP2, hP3⟩

theorem Topology.P3_union_right_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hPA : Topology.P3 (X := X) A) (hB_open : IsOpen (B : Set X)) :
    Topology.P3 (X := X) (A ∪ B) := by
  -- Any open set satisfies `P3`.
  have hPB : Topology.P3 (X := X) B :=
    Topology.isOpen_subset_interiorClosure (X := X) (A := B) hB_open
  -- Combine the two `P3` hypotheses using the existing union lemma.
  exact Topology.P3_union (X := X) (A := A) (B := B) hPA hPB

theorem Topology.P2_iff_closure_eq_closureInterior_and_P3 {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A ↔
      (closure (A : Set X) = closure (interior A) ∧ Topology.P3 (X := X) A) := by
  -- Step 1: use the existing equivalence between `P2` and `P1 ∧ P3`.
  have h₁ :=
    Topology.P2_iff_P1_and_P3 (X := X) (A := A)
  -- Step 2: rewrite the `P1` component via the closure‐equality characterization.
  have h₂ :
      (Topology.P1 (X := X) A ∧ Topology.P3 (X := X) A) ↔
        (closure (A : Set X) = closure (interior A) ∧ Topology.P3 (X := X) A) := by
    constructor
    · rintro ⟨hP1, hP3⟩
      have h_eq :=
        (Topology.P1_iff_closure_eq_closureInterior (X := X) (A := A)).1 hP1
      exact ⟨h_eq, hP3⟩
    · rintro ⟨h_eq, hP3⟩
      have hP1 :
          Topology.P1 (X := X) A :=
        (Topology.P1_iff_closure_eq_closureInterior (X := X) (A := A)).2 h_eq
      exact ⟨hP1, hP3⟩
  exact h₁.trans h₂

theorem Topology.P1_implies_interior_closure_subset_closureInterior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X:=X) A →
      interior (closure (A : Set X)) ⊆ closure (interior A) := by
  intro hP1
  -- Translate `P1` into the equality of the two closures.
  have h_eq : closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closureInterior (X := X) (A := A)).1 hP1
  intro x hx
  -- Rewrite `hx` using `h_eq`.
  have hx' : x ∈ interior (closure (interior A)) := by
    simpa [h_eq] using hx
  -- Conclude with the basic inclusion `interior ⊆ closure`.
  exact
    (interior_subset :
      interior (closure (interior A)) ⊆ closure (interior A)) hx'

theorem Topology.closed_dense_interior_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) (h_dense : Dense (A : Set X)) :
    interior (A : Set X) = (Set.univ : Set X) := by
  have h_eq : (A : Set X) = (Set.univ : Set X) :=
    Topology.closed_dense_eq_univ (X := X) (A := A) h_closed h_dense
  simpa [h_eq, interior_univ]

theorem Topology.closure_inter_interiors_subset_inter_closure_interior {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure ((interior (A : Set X)) ∩ interior B) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  have hxA : x ∈ closure (interior A) :=
    (closure_mono
        (Set.inter_subset_left :
          (interior (A : Set X) ∩ interior B : Set X) ⊆ interior A)) hx
  have hxB : x ∈ closure (interior B) :=
    (closure_mono
        (Set.inter_subset_right :
          (interior (A : Set X) ∩ interior B : Set X) ⊆ interior B)) hx
  exact ⟨hxA, hxB⟩

theorem Topology.closure_subset_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) ⊆ (Set.univ : Set X) := by
  intro x hx
  simp

theorem Topology.interior_closure_interiorClosure_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (A : Set X)))) ⊆
      closure (interior (closure A)) := by
  intro x hx
  -- `interior S ⊆ S` for every set `S`, and `S ⊆ closure S`.
  -- Combining the two inclusions for `S = closure (interior (closure A))`
  -- yields the desired result.
  exact
    (interior_subset :
      interior (closure (interior (closure (A : Set X)))) ⊆
        closure (interior (closure A))) hx

theorem Topology.interior_closure_iterate_eight_eq_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure
      (interior (closure
        (interior (closure
          (interior (closure
            (interior (closure
              (interior (closure
                (interior (closure (A : Set X))))
              ))
            ))
          ))
        ))
      )) =
      interior (closure A) := by
  simp
    [Topology.interior_closure_iterate_seven_eq_interior_closure (X := X) (A := A),
     Topology.interior_closure_interior_closure_eq_interior_closure (X := X) (A := A)]

theorem Topology.P2_and_emptyInteriorClosureInterior_implies_empty {X : Type*}
    [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A)
    (h_int : interior (closure (interior (A : Set X))) = (∅ : Set X)) :
    (A : Set X) = (∅ : Set X) := by
  -- From `P2`, every point of `A` lies in `interior (closure (interior A))`,
  -- which is empty by assumption, hence `A` itself must be empty.
  have h_subset : (A : Set X) ⊆ (∅ : Set X) := by
    intro x hxA
    have : (x : X) ∈ interior (closure (interior (A : Set X))) := hP2 hxA
    simpa [h_int] using this
  exact Set.Subset.antisymm h_subset (Set.empty_subset _)

theorem Topology.interior_diff_subset_interior {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior ((A \ B) : Set X) ⊆ interior A := by
  intro x hx
  have h_subset : ((A \ B) : Set X) ⊆ A := by
    intro y hy
    exact hy.1
  exact (interior_mono h_subset) hx

theorem Topology.interior_interior_interior_eq_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (interior (interior (A : Set X))) = interior A := by
  simp [interior_interior]

theorem Topology.interior_inter_closure_eq_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (interior (A : Set X)) ∩ closure A = interior A := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    have hxA : (x : X) ∈ A :=
      (interior_subset : interior (A : Set X) ⊆ A) hx
    have hxCl : (x : X) ∈ closure A := subset_closure hxA
    exact ⟨hx, hxCl⟩

theorem Topology.interior_closure_iterate_nine_eq_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure
      (interior (closure
        (interior (closure
          (interior (closure
            (interior (closure
              (interior (closure
                (interior (closure (A : Set X))))
              ))
            ))
          ))
        ))
      )) =
      interior (closure A) := by
  -- First, collapse the innermost eight-layer expression using the existing lemma.
  have h8 :=
    Topology.interior_closure_iterate_eight_eq_interior_closure (X := X) (A := A)
  -- After rewriting with `h8`, we are left with `interior (closure (interior (closure A)))`,
  -- which simplifies via the two-layer idempotency lemma.
  simpa [h8,
        Topology.interior_closure_interior_closure_eq_interior_closure
          (X := X) (A := A)]

theorem Topology.P3_closureInterior_iff_isOpen_closureInterior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (closure (interior (A : Set X))) ↔
      IsOpen (closure (interior (A : Set X))) := by
  -- `closure (interior A)` is always a closed set.
  have h_closed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  -- Apply the generic equivalence between `P3` and openness for closed sets.
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed
      (X := X) (A := closure (interior (A : Set X))) h_closed)

theorem Topology.P1_iff_subset_closureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X:=X) A ↔ A ⊆ closure (interior A) := by
  rfl

theorem Topology.closure_inter_closureInterior_eq_closureInterior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    (closure (A : Set X)) ∩ closure (interior A) = closure (interior A) := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    have hx₁ : (x : X) ∈ closure (A : Set X) :=
      (Topology.closure_interior_subset_closure (X := X) (A := A)) hx
    exact And.intro hx₁ hx

theorem Topology.P1_union_left_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen (A : Set X)) (hPB : Topology.P1 (X := X) B) :
    Topology.P1 (X := X) (A ∪ B) := by
  -- Swap the roles of `A` and `B` and apply the existing lemma.
  have h :=
    Topology.P1_union_right_of_open (X := X) (A := B) (B := A) hPB hA_open
  simpa [Set.union_comm] using h

theorem Topology.interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ closure A := by
  intro x hx
  have hxA : (x : X) ∈ A := interior_subset hx
  exact subset_closure hxA

theorem Topology.P2_iff_P1_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (X:=X) A) :
    Topology.P2 (X:=X) A ↔ Topology.P1 (X:=X) A := by
  -- Start from the general equivalence `P2 ↔ P1 ∧ P3`.
  have h := Topology.P2_iff_P1_and_P3 (X := X) (A := A)
  -- Since `hP3` is assumed, `P1 ∧ P3` is equivalent to `P1`.
  have h_aux :
      (Topology.P1 (X:=X) A ∧ Topology.P3 (X:=X) A) ↔
        Topology.P1 (X:=X) A := by
    constructor
    · intro h'
      exact h'.1
    · intro hP1
      exact And.intro hP1 hP3
  -- Combine the two equivalences.
  simpa using h.trans h_aux

theorem Topology.closure_union_interior_subset_closure_interior_union {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure ((interior (A : Set X)) ∪ interior B) ⊆
      closure (interior (A ∪ B)) := by
  -- The union of the interiors is contained in the interior of the union.
  have h_subset :
      (interior (A : Set X) ∪ interior B) ⊆ interior (A ∪ B) :=
    Topology.union_interior_subset_interior_union (X := X) (A := A) (B := B)
  -- Taking closures preserves inclusions.
  exact closure_mono h_subset

theorem Topology.compl_closure_inter_self_nonempty_iff {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (((closure (A : Set X))ᶜ) ∩ A : Set X).Nonempty ↔ False := by
  constructor
  · intro hne
    rcases hne with ⟨x, ⟨hx_not_cl, hxA⟩⟩
    have : (x : X) ∈ closure (A : Set X) := subset_closure hxA
    exact hx_not_cl this
  · intro hFalse
    cases hFalse

theorem Topology.dense_implies_interior_closureInterior_closure_eq_univ {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) →
      interior (closure (interior (closure (A : Set X)))) = (Set.univ : Set X) := by
  intro hDense
  have h_cl : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  calc
    interior (closure (interior (closure (A : Set X))))
        = interior (closure (interior (Set.univ : Set X))) := by
          simpa [h_cl]
    _ = interior (closure (Set.univ : Set X)) := by
          simp [interior_univ]
    _ = interior (Set.univ : Set X) := by
          simp [closure_univ]
    _ = (Set.univ : Set X) := by
          simp [interior_univ]

theorem Topology.P1_interiorClosureInteriorClosure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (X := X) (interior (closure (interior (closure (A : Set X))))) := by
  -- The set under consideration is an interior, hence it is open.
  have h_open :
      IsOpen (interior (closure (interior (closure (A : Set X))))) :=
    isOpen_interior
  -- Every open set satisfies `P1`.
  exact
    Topology.isOpen_subset_closureInterior
      (X := X)
      (A := interior (closure (interior (closure (A : Set X))))) h_open

theorem Topology.closure_interior_iterate_eight_eq_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior (closure (interior (A : Set X)))))))) =
      closure (interior A) := by
  simp [Topology.closure_interior_closure_interior_eq_closure_interior,
        Topology.closure_interior_closure_interior_closure_eq_closure_interior_closure,
        closure_closure]

theorem Topology.P3_iff_subset_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) A ↔ (A ⊆ interior (closure A)) := by
  rfl

theorem Topology.P2_closureInterior_iff_isOpen_closureInterior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure (interior (A : Set X))) ↔
      IsOpen (closure (interior (A : Set X))) := by
  -- `closure (interior A)` is always closed.
  have h_closed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  -- Apply the general equivalence for closed sets.
  simpa using
    (Topology.P2_iff_isOpen_of_isClosed
      (X := X) (A := closure (interior (A : Set X))) h_closed)

theorem Topology.closure_inter_subset_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure ((A ∩ B) : Set X) ⊆ closure (A : Set X) := by
  -- `A ∩ B` is contained in `A`, so applying `closure` (a monotone operator)
  -- yields the desired inclusion.
  exact closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)

theorem Topology.interior_closure_iterate_ten_eq_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure
      (interior (closure
        (interior (closure
          (interior (closure
            (interior (closure
              (interior (closure
                (interior (closure
                  (interior (closure (A : Set X))))
                ))
              ))
            ))
          ))
        ))
      )) =
      interior (closure A) := by
  -- Collapse the innermost nine-layer expression using the existing lemma.
  have h₁ :=
    Topology.interior_closure_iterate_nine_eq_interior_closure (X := X) (A := A)
  -- Rewrite and finish with the two-layer idempotency lemma.
  simpa [h₁,
    Topology.interior_closure_interior_closure_eq_interior_closure
      (X := X) (A := A)]

theorem Topology.closure_eq_univ_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (A : Set X) = (Set.univ : Set X)) :
    Topology.P3 (X := X) A := by
  dsimp [Topology.P3]
  intro x hxA
  -- `x` is certainly in the closure of `A`.
  have hx_cl : (x : X) ∈ closure (A : Set X) := subset_closure hxA
  -- Rewrite using the hypothesis `h` and simplify.
  simpa [h, interior_univ] using hx_cl

theorem Topology.P2_iff_subset_interiorClosureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 (X := X) A ↔ A ⊆ interior (closure (interior A)) := by
  rfl

theorem Topology.denseInterior_implies_P2_closureInterior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) →
      Topology.P2 (X := X) (closure (interior (A : Set X))) := by
  intro hDense
  -- The density assumption yields `closure (interior A) = univ`.
  have h_closure : closure (interior (A : Set X)) = (Set.univ : Set X) :=
    hDense.closure_eq
  -- `P2` holds for `univ`, and rewriting via `h_closure` gives the desired result.
  simpa [h_closure] using Topology.P2_univ (X := X)

theorem Topology.closure_inter_interior_subset_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure ((A ∩ interior B) : Set X) ⊆ closure (A : Set X) := by
  -- Since `A ∩ interior B ⊆ A`, monotonicity of `closure` gives the claim.
  have h_subset : ((A ∩ interior B) : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  exact closure_mono h_subset

theorem Topology.all_P_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (X := X) (∅ : Set X) ∧
      Topology.P2 (X := X) (∅ : Set X) ∧
        Topology.P3 (X := X) (∅ : Set X) := by
  exact
    ⟨Topology.P1_empty (X := X), Topology.P2_empty (X := X),
      Topology.P3_empty (X := X)⟩

theorem Topology.closure_inter_subset_right {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((A ∩ B) : Set X) ⊆ closure (B : Set X) := by
  -- Since `A ∩ B ⊆ B`, monotonicity of `closure` yields the desired inclusion.
  have h_subset : ((A ∩ B) : Set X) ⊆ (B : Set X) := by
    intro x hx
    exact hx.2
  exact closure_mono h_subset



theorem Topology.interior_closure_iterate_eleven_eq_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure
      (interior (closure
        (interior (closure
          (interior (closure
            (interior (closure
              (interior (closure
                (interior (closure
                  (interior (closure (A : Set X))))
                ))
              ))
            ))
          ))
        ))
      )) =
      interior (closure A) := by
  -- First, collapse the innermost ten-layer expression using the existing lemma.
  have h₁ :=
    Topology.interior_closure_iterate_ten_eq_interior_closure (X := X) (A := A)
  -- Rewrite the goal using `h₁`, then finish with the two-layer idempotency lemma.
  calc
    interior (closure
      (interior (closure
        (interior (closure
          (interior (closure
            (interior (closure
              (interior (closure
                (interior (closure
                  (interior (closure (A : Set X))))
                ))
              ))
            ))
          ))
        ))
      )) =
        interior (closure (interior (closure A))) := by
          simpa [h₁]
    _ = interior (closure A) := by
          simpa using
            (Topology.interior_closure_interior_closure_eq_interior_closure
              (X := X) (A := A))

theorem Topology.P3_union_left_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen (A : Set X)) (hPB : Topology.P3 (X := X) B) :
    Topology.P3 (X := X) (A ∪ B) := by
  -- Apply the “right” version with the roles of `A` and `B` swapped,
  -- then rewrite using commutativity of `∪`.
  have h :=
    Topology.P3_union_right_of_open (X := X) (A := B) (B := A) hPB hA_open
  simpa [Set.union_comm] using h

theorem Topology.closure_eq_closureInterior_and_closureInteriorClosure_of_P1_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X:=X) A →
      Topology.P3 (X:=X) A →
        (closure (A : Set X) = closure (interior A)) ∧
          (closure (A : Set X) = closure (interior (closure A))) := by
  intro hP1 hP3
  have h₁ : closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closureInterior (X := X) (A := A)).1 hP1
  have h₂ : closure (A : Set X) = closure (interior (closure A)) :=
    Topology.P3_implies_closure_eq_closureInteriorClosure (X := X) (A := A) hP3
  exact And.intro h₁ h₂

theorem Topology.P2_iff_P3_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X:=X) A) :
    Topology.P2 (X:=X) A ↔ Topology.P3 (X:=X) A := by
  -- Start from the general equivalence `P2 ↔ P1 ∧ P3`.
  have h := Topology.P2_iff_P1_and_P3 (X:=X) (A:=A)
  -- Given `hP1`, the conjunction `P1 ∧ P3` is equivalent to `P3`.
  have h_aux :
      (Topology.P1 (X:=X) A ∧ Topology.P3 (X:=X) A) ↔
        Topology.P3 (X:=X) A := by
    constructor
    · intro h'
      exact h'.2
    · intro hP3
      exact And.intro hP1 hP3
  -- Combine the two equivalences.
  simpa using h.trans h_aux

theorem Topology.P3_iff_P2_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X:=X) A) :
    Topology.P3 (X:=X) A ↔ Topology.P2 (X:=X) A := by
  constructor
  · intro hP3
    -- Combine the given `P1` with the assumed `P3` to obtain `P2`.
    have hPair : Topology.P1 (X:=X) A ∧ Topology.P3 (X:=X) A := ⟨hP1, hP3⟩
    exact
      (Topology.P2_iff_P1_and_P3 (X:=X) (A:=A)).2 hPair
  · intro hP2
    -- Extract `P3` from `P2`.
    have hPair : Topology.P1 (X:=X) A ∧ Topology.P3 (X:=X) A :=
      (Topology.P2_iff_P1_and_P3 (X:=X) (A:=A)).1 hP2
    exact hPair.2

theorem Topology.interior_eq_compl_closure_compl {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (A : Set X) = (closure (Aᶜ) : Set X)ᶜ := by
  simpa [compl_compl] using
    (interior_compl (s := (Aᶜ : Set X)))

theorem Topology.P1_and_dense_implies_denseInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (X := X) A → Dense (A : Set X) → Dense (interior (A : Set X)) := by
  intro hP1 hDenseA
  dsimp [Dense] at hDenseA ⊢
  -- `P1` gives equality of closures.
  have h_cl_eq : closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closureInterior (X := X) (A := A)).1 hP1
  -- Rewrite the density statement using `h_cl_eq`.
  simpa [h_cl_eq] using hDenseA

theorem Topology.P1_implies_closureInteriorClosureInterior_eq_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) A →
      closure (interior (closure (interior (A : Set X)))) = closure (A : Set X) := by
  intro hP1
  -- First, collapse the nested `closure ∘ interior` expression.
  have h₁ :
      closure (interior (closure (interior (A : Set X)))) =
        closure (interior A) :=
    Topology.closure_interior_closure_interior_eq_closure_interior (X := X) (A := A)
  -- Next, identify `closure (interior A)` with `closure A` using `P1`.
  have h₂ :
      closure (interior (A : Set X)) = closure (A : Set X) := by
    simpa using
      ((Topology.P1_iff_closure_eq_closureInterior (X := X) (A := A)).1 hP1).symm
  -- Combine the two equalities.
  simpa [h₂] using h₁

theorem Topology.closure_compl_eq_compl_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (Aᶜ : Set X) = (interior (A : Set X))ᶜ := by
  -- Start from the existing relationship between `interior` and `closure` of complements.
  have h : interior (A : Set X) = (closure (Aᶜ : Set X))ᶜ :=
    Topology.interior_eq_compl_closure_compl (A := A)
  -- Taking complements on both sides yields the desired identity.
  simpa using (congrArg Set.compl h).symm

theorem Topology.interior_compl_eq_compl_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior ((A : Set X)ᶜ) = (closure (A : Set X))ᶜ := by
  simpa [compl_compl] using
    (Topology.interior_eq_compl_closure_compl (X := X) (A := ((A : Set X)ᶜ)))

theorem Topology.P1_iff_empty_of_emptyInterior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_int : interior (A : Set X) = (∅ : Set X)) :
    Topology.P1 (X := X) A ↔ (A : Set X) = (∅ : Set X) := by
  constructor
  · intro hP1
    exact
      Topology.P1_and_emptyInterior_implies_empty (X := X) (A := A) hP1 h_int
  · intro hA
    simpa [hA] using Topology.P1_empty (X := X)

theorem Topology.nonempty_closureInterior_iff_nonempty_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    (closure (interior (A : Set X))).Nonempty ↔ (interior (A : Set X)).Nonempty := by
  classical
  constructor
  · intro h_nonempty_cl
    -- `closure (interior A)` is not empty.
    have h_cl_ne : closure (interior (A : Set X)) ≠ (∅ : Set X) :=
      (Set.nonempty_iff_ne_empty).1 h_nonempty_cl
    -- If `interior A` were empty, the equivalence would force its closure to be empty,
    -- contradicting `h_cl_ne`.
    have h_int_ne : interior (A : Set X) ≠ (∅ : Set X) := by
      intro h_int_eq
      have h_cl_eq : closure (interior (A : Set X)) = (∅ : Set X) :=
        ((Topology.closureInterior_eq_empty_iff (X := X) (A := A)).2 h_int_eq)
      exact h_cl_ne h_cl_eq
    exact (Set.nonempty_iff_ne_empty).2 h_int_ne
  · intro h_nonempty_int
    rcases h_nonempty_int with ⟨x, hx⟩
    exact ⟨x, subset_closure hx⟩

theorem Topology.P1_iff_P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X:=X) A) :
    Topology.P1 (X:=X) A ↔ Topology.P3 (X:=X) A := by
  -- From the given `P2`, we immediately obtain both `P1` and `P3`.
  have hP1 : Topology.P1 (X:=X) A :=
    Topology.P2_implies_P1 (X:=X) (A:=A) hP2
  have hP3 : Topology.P3 (X:=X) A :=
    Topology.P2_implies_P3 (X:=X) (A:=A) hP2
  -- These witnesses let us establish the equivalence.
  exact ⟨fun _ => hP3, fun _ => hP1⟩

theorem Topology.closure_interInterior_subset_inter_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure ((A ∩ interior B) : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  -- `x` lies in `closure A` because `A ∩ interior B ⊆ A`.
  have hxA : (x : X) ∈ closure A :=
    (closure_mono (Set.inter_subset_left : (A ∩ interior B : Set X) ⊆ A)) hx
  -- `x` lies in `closure B` because `A ∩ interior B ⊆ B`.
  have hxB : (x : X) ∈ closure B := by
    have h_subset : ((A ∩ interior B) : Set X) ⊆ B := by
      intro y hy
      exact (interior_subset : interior B ⊆ B) hy.2
    exact (closure_mono h_subset) hx
  exact ⟨hxA, hxB⟩

theorem Topology.all_P_compl_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P1 (X := X) (Aᶜ : Set X) ∧
      Topology.P2 (X := X) (Aᶜ : Set X) ∧
        Topology.P3 (X := X) (Aᶜ : Set X) := by
  -- The complement of a closed set is open.
  have hA_open_compl : IsOpen (Aᶜ : Set X) := hA_closed.isOpen_compl
  -- Any open set satisfies all three properties `P1`, `P2`, and `P3`.
  exact
    Topology.isOpen_implies_all_P (X := X) (A := Aᶜ) hA_open_compl

theorem Topology.closure_interior_iterate_nine_eq_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (interior
      (closure (interior
        (closure (interior
          (closure (interior
            (closure (interior
              (closure (interior (A : Set X))))
            ))
          ))
        )))) =
      closure (interior A) := by
  -- Collapse the innermost eight-layer expression.
  have h₁ :=
    Topology.closure_interior_iterate_eight_eq_closure_interior
      (X := X) (A := A)
  -- Rewrite using `h₁` and apply the two-layer idempotency lemma.
  calc
    closure (interior
      (closure (interior
        (closure (interior
          (closure (interior
            (closure (interior
              (closure (interior (A : Set X))))
            ))
          ))
        )))) =
        closure (interior (closure (interior A))) := by
          simpa [h₁]
    _ = closure (interior A) := by
          simpa using
            (Topology.closure_interior_closure_interior_eq_closure_interior
              (X := X) (A := A))

theorem Topology.P2_closureInterior_iff_P3_closureInterior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure (interior (A : Set X))) ↔
      Topology.P3 (X := X) (closure (interior (A : Set X))) := by
  -- Both sides are equivalent to the openness of `closure (interior A)`.
  have hP2 :=
    Topology.P2_closureInterior_iff_isOpen_closureInterior (X := X) (A := A)
  have hP3 :=
    Topology.P3_closureInterior_iff_isOpen_closureInterior (X := X) (A := A)
  simpa using hP2.trans hP3.symm

theorem Topology.closure_interior_inter_subset_inter_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure ((interior (A : Set X)) ∩ B) ⊆
      closure (interior A) ∩ closure B := by
  intro x hx
  have hxA : x ∈ closure (interior A) := by
    -- `interior A ∩ B` is contained in `interior A`
    have h_subset : ((interior (A : Set X)) ∩ B : Set X) ⊆ interior A := by
      intro y hy
      exact hy.1
    exact (closure_mono h_subset) hx
  have hxB : x ∈ closure B := by
    -- `interior A ∩ B` is contained in `B`
    have h_subset : ((interior (A : Set X)) ∩ B : Set X) ⊆ B := by
      intro y hy
      exact hy.2
    exact (closure_mono h_subset) hx
  exact ⟨hxA, hxB⟩

theorem Topology.denseInterior_implies_closureInterior_eq_univ {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) →
      closure (interior (A : Set X)) = (Set.univ : Set X) := by
  intro hDense
  simpa using hDense.closure_eq

theorem Topology.P2_implies_subset_interiorClosure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 (X:=X) A → (A : Set X) ⊆ interior (closure A) := by
  intro hP2
  -- From `P2` we obtain `P3`, which is precisely the desired inclusion.
  have hP3 : Topology.P3 (X:=X) A :=
    Topology.P2_implies_P3 (X:=X) (A:=A) hP2
  simpa [Topology.P3] using hP3

theorem Topology.interior_closure_iterate_twelve_eq_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure
      (interior (closure
        (interior (closure
          (interior (closure
            (interior (closure
              (interior (closure
                (interior (closure
                  (interior (closure
                    (interior (closure
                      (interior (closure (A : Set X))))
                    ))
                  ))
                ))
              ))
            ))
          ))
        ))
      )) =
      interior (closure A) := by
  -- Collapse the innermost eleven-layer expression using the existing lemma.
  have h₁ :=
    Topology.interior_closure_iterate_eleven_eq_interior_closure (X := X) (A := A)
  -- Rewrite and finish with the two-layer idempotency lemma.
  simpa [h₁,
        Topology.interior_closure_interior_closure_eq_interior_closure
          (X := X) (A := A)]

theorem Topology.closureInterior_univ_implies_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P1 (X := X) A := by
  dsimp [Topology.P1]
  intro x hx
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [h] using this

theorem Topology.closure_inter_closure_subset_inter_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure ((A ∩ closure (B : Set X)) : Set X) ⊆
      closure A ∩ closure B := by
  intro x hx
  -- Membership in `closure A` follows from monotonicity of `closure`.
  have hxA : (x : X) ∈ closure A :=
    (closure_mono
        (Set.inter_subset_left :
          (A ∩ closure (B : Set X) : Set X) ⊆ A)) hx
  -- Membership in `closure B` is obtained similarly.
  have hxB : (x : X) ∈ closure B := by
    -- First, view `closure B` as a superset of the intersection.
    have h₁ :
        (A ∩ closure (B : Set X) : Set X) ⊆ closure B :=
      Set.inter_subset_right
    have hxB' : (x : X) ∈ closure (closure (B : Set X)) :=
      (closure_mono h₁) hx
    simpa [closure_closure] using hxB'
  exact And.intro hxA hxB

theorem Topology.interior_inter_closure_subset_interior_and_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    interior ((A ∩ closure (B : Set X)) : Set X) ⊆ interior A ∩ closure B := by
  intro x hx
  -- First, record that `x` lies in `A ∩ closure B`.
  have h_mem : (x : X) ∈ A ∩ closure (B : Set X) := interior_subset hx
  -- Deduce `x ∈ interior A` using monotonicity of `interior`.
  have hxA : (x : X) ∈ interior A := by
    have h_subset : (A ∩ closure (B : Set X) : Set X) ⊆ A :=
      Set.inter_subset_left
    exact (interior_mono h_subset) hx
  -- Extract the `closure B` membership from `h_mem`.
  have hxB : (x : X) ∈ closure B := h_mem.2
  exact And.intro hxA hxB

theorem Topology.interior_closure_closure_interior_eq_interior_closureInterior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure (closure (interior (A : Set X)))) =
      interior (closure (interior A)) := by
  simpa [closure_closure]

theorem Topology.closure_eq_compl_interior_compl {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (A : Set X) = (interior (Aᶜ : Set X))ᶜ := by
  -- Start with `interior (Aᶜ) = (closure A)ᶜ` and take complements.
  have h : interior ((Aᶜ : Set X)) = (closure (A : Set X))ᶜ :=
    Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  simpa [compl_compl] using (congrArg Set.compl h).symm

theorem Topology.P1_iff_P2_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (X:=X) A) :
    Topology.P1 (X:=X) A ↔ Topology.P2 (X:=X) A := by
  have h := (Topology.P2_iff_P1_of_P3 (X:=X) (A:=A) hP3)
  simpa using h.symm

theorem Topology.isClosed_boundary {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (closure (A : Set X) \ interior A) := by
  -- The closure of a set is closed.
  have h₁ : IsClosed (closure (A : Set X)) := isClosed_closure
  -- The complement of the interior is closed.
  have h₂ : IsClosed ((interior (A : Set X))ᶜ) := by
    have : IsOpen (interior (A : Set X)) := isOpen_interior
    exact this.isClosed_compl
  -- Express the set as an intersection of two closed sets.
  simpa [Set.diff_eq] using h₁.inter h₂

theorem Topology.closure_subset_closure_union_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A : Set X) ⊆ closure (A ∪ B) := by
  exact closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)

theorem Topology.closure_subset_closure_union_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (B : Set X) ⊆ closure (A ∪ B) := by
  -- Apply the “left‐hand” version after swapping `A` and `B`,
  -- then rewrite using commutativity of `∪`.
  have h :
      closure (B : Set X) ⊆ closure (B ∪ A) :=
    Topology.closure_subset_closure_union_left (X := X) (A := B) (B := A)
  simpa [Set.union_comm] using h

theorem Topology.isOpen_closure_iff_interior_closure_eq_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) ↔
      interior (closure (A : Set X)) = closure (A : Set X) := by
  constructor
  · intro h_open
    simpa using h_open.interior_eq
  · intro h_eq
    have h_open_int : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    simpa [h_eq] using h_open_int

theorem Topology.closure_inter_closures_eq_inter_closures {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (closure (A : Set X) ∩ closure B) = closure A ∩ closure B := by
  -- The intersection of two closed sets is closed.
  have h_closed : IsClosed (closure (A : Set X) ∩ closure B) :=
    (isClosed_closure : IsClosed (closure (A : Set X))).inter
      (isClosed_closure : IsClosed (closure B))
  -- Taking the closure of a closed set yields the set itself.
  simpa using h_closed.closure_eq

theorem Topology.P2_union_left_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen (A : Set X)) (hPB : Topology.P2 (X := X) B) :
    Topology.P2 (X := X) (A ∪ B) := by
  -- `A` is open, hence it satisfies `P2`.
  have hPA : Topology.P2 (X := X) A :=
    isOpen_implies_P2 (X := X) (A := A) hA_open
  -- Combine the two `P2` hypotheses using the existing union lemma.
  exact Topology.P2_union (X := X) (A := A) (B := B) hPA hPB

theorem Topology.interior_closure_iterate_thirteen_eq_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure
      (interior (closure
        (interior (closure
          (interior (closure
            (interior (closure
              (interior (closure
                (interior (closure
                  (interior (closure
                    (interior (closure
                      (interior (closure
                        (interior (closure (A : Set X))))
                      ))
                    ))
                  ))
                ))
              ))
            ))
          ))
        ))
      )) =
      interior (closure A) := by
  -- Collapse the innermost twelve‐layer expression using the existing lemma.
  have h :=
    Topology.interior_closure_iterate_twelve_eq_interior_closure (X := X) (A := A)
  -- Rewrite and finish with the two‐layer idempotency lemma.
  simpa [h,
        Topology.interior_closure_interior_closure_eq_interior_closure
          (X := X) (A := A)]

theorem Topology.boundary_empty_iff_isClopen {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ interior A = (∅ : Set X) ↔
      (IsOpen (A : Set X) ∧ IsClosed (A : Set X)) := by
  classical
  constructor
  · intro hEmpty
    -- First, show `closure A ⊆ interior A`.
    have h_subset : closure (A : Set X) ⊆ interior A := by
      intro x hx_cl
      by_contra h_int
      have hx_diff : x ∈ closure (A : Set X) \ interior A := ⟨hx_cl, h_int⟩
      have : x ∈ (∅ : Set X) := by
        simpa [hEmpty] using hx_diff
      exact (Set.not_mem_empty _ this)
    -- Deduce `interior A = A`.
    have h_int_eq : interior (A : Set X) = A := by
      apply Set.Subset.antisymm
      · exact interior_subset
      · intro x hxA
        exact h_subset (subset_closure hxA)
    -- Deduce `closure A = A`.
    have h_cl_eq : closure (A : Set X) = A := by
      apply Set.Subset.antisymm
      · have : closure (A : Set X) ⊆ interior A := h_subset
        simpa [h_int_eq] using this
      · exact subset_closure
    -- Conclude that `A` is both open and closed.
    have h_open : IsOpen (A : Set X) := by
      simpa [h_int_eq] using (isOpen_interior : IsOpen (interior (A : Set X)))
    have h_closed : IsClosed (A : Set X) := by
      simpa [h_cl_eq] using (isClosed_closure : IsClosed (closure (A : Set X)))
    exact And.intro h_open h_closed
  · rintro ⟨h_open, h_closed⟩
    have h_int_eq : interior (A : Set X) = A := h_open.interior_eq
    have h_cl_eq  : closure (A : Set X) = A := h_closed.closure_eq
    simpa [h_int_eq, h_cl_eq, Set.diff_self]

theorem Topology.P1_iff_boundary_subset_closureInterior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) A ↔
      (closure (A : Set X) \ interior A) ⊆ closure (interior A) := by
  -- First, recall the existing characterization of `P1`.
  have h_equiv :
      Topology.P1 (X := X) A ↔
        closure (A : Set X) ⊆ closure (interior A) :=
    Topology.P1_iff_closure_subset_closureInterior (X := X) (A := A)
  constructor
  · -- `P1` immediately yields the desired boundary inclusion.
    intro hP1
    have h_closure : closure (A : Set X) ⊆ closure (interior A) :=
      (h_equiv).1 hP1
    intro x hx
    exact h_closure hx.1
  · -- Conversely, assume the boundary is included; prove the closure inclusion.
    intro h_boundary
    have h_closure : closure (A : Set X) ⊆ closure (interior A) := by
      intro x hx_cl
      by_cases hx_int : (x : X) ∈ interior A
      · -- Points of the interior are certainly in the closure of the interior.
        exact subset_closure hx_int
      · -- Otherwise, the point lies in the boundary, which is assumed to be included.
        have hx_bd : (x : X) ∈ closure (A : Set X) \ interior A :=
          ⟨hx_cl, hx_int⟩
        exact h_boundary hx_bd
    exact (h_equiv).2 h_closure

theorem Topology.closure_interior_union_closure_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior (A : Set X)) ∪ closure A = closure A := by
  ext x
  constructor
  · intro hx
    cases hx with
    | inr h_clA => exact h_clA
    | inl h_clIntA =>
        exact
          (Topology.closure_interior_subset_closure (X := X) (A := A)) h_clIntA
  · intro hx
    exact Or.inr hx

theorem Topology.boundary_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (A : Set X) \ interior A) ⊆ closure A := by
  intro x hx
  exact hx.1

theorem Topology.closure_compl_eq_compl_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_open : IsOpen (A : Set X)) :
    closure ((A : Set X)ᶜ) = (A : Set X)ᶜ := by
  -- The complement of an open set is closed.
  have h_closed : IsClosed ((A : Set X)ᶜ) := hA_open.isClosed_compl
  -- The closure of a closed set is the set itself.
  simpa using h_closed.closure_eq

theorem Topology.boundary_eq_diff_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    closure (A : Set X) \ interior A = (A : Set X) \ interior A := by
  simpa [hA_closed.closure_eq]

theorem Topology.boundary_eq_closure_diff_self_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_open : IsOpen (A : Set X)) :
    closure (A : Set X) \ interior A = closure (A : Set X) \ A := by
  simpa [hA_open.interior_eq]

theorem Topology.boundary_empty_of_isClopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_open : IsOpen (A : Set X)) (hA_closed : IsClosed (A : Set X)) :
    closure (A : Set X) \ interior A = (∅ : Set X) := by
  have h_int : interior (A : Set X) = A := hA_open.interior_eq
  have h_cl : closure (A : Set X) = A := hA_closed.closure_eq
  simpa [h_int, h_cl, Set.diff_self]

theorem Topology.closureInterior_union_interiorClosure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) ∪ interior (closure A) ⊆ closure A := by
  intro x hx
  cases hx with
  | inl h_closureInt =>
      -- `closure (interior A)` is contained in `closure A`
      have h_subset : closure (interior (A : Set X)) ⊆ closure A :=
        closure_mono (interior_subset : interior (A : Set X) ⊆ A)
      exact h_subset h_closureInt
  | inr h_interiorCl =>
      -- `interior (closure A)` is contained in `closure A`
      exact (interior_subset : interior (closure A) ⊆ closure A) h_interiorCl

theorem Topology.all_P_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hA_dense : Dense (A : Set X)) :
    Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A ∧ Topology.P3 (X := X) A := by
  have hP1 : Topology.P1 (X := X) A :=
    Topology.closed_dense_implies_P1 (X := X) (A := A) hA_closed hA_dense
  have hP2 : Topology.P2 (X := X) A :=
    Topology.closed_dense_implies_P2 (X := X) (A := A) hA_closed hA_dense
  have hP3 : Topology.P3 (X := X) A :=
    Topology.closed_dense_implies_P3 (X := X) (A := A) hA_closed hA_dense
  exact ⟨hP1, hP2, hP3⟩

theorem Dense.closure_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Dense (A : Set X)) : closure (A : Set X) = (Set.univ : Set X) := by
  ext x
  constructor
  · intro _; simp
  · intro _; exact h x

theorem Topology.isOpen_closureInterior_iff_interior_closureInterior_eq_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (interior (A : Set X))) ↔
      interior (closure (interior A)) = closure (interior A) := by
  constructor
  · intro h_open
    simpa using h_open.interior_eq
  · intro h_eq
    have h_open_int : IsOpen (interior (closure (interior (A : Set X)))) :=
      isOpen_interior
    simpa [h_eq] using h_open_int

theorem Topology.interior_closure_inter_closures_subset_inter_interior_closures
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior ((closure (A : Set X)) ∩ closure B) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- `closure A ∩ closure B` is contained in `closure A`.
  have h_subsetA :
      (closure (A : Set X) ∩ closure B : Set X) ⊆ closure A :=
    Set.inter_subset_left
  -- `closure A ∩ closure B` is also contained in `closure B`.
  have h_subsetB :
      (closure (A : Set X) ∩ closure B : Set X) ⊆ closure B :=
    Set.inter_subset_right
  -- Apply the monotonicity of `interior` to obtain both components.
  have hxA : (x : X) ∈ interior (closure A) :=
    (interior_mono h_subsetA) hx
  have hxB : (x : X) ∈ interior (closure B) :=
    (interior_mono h_subsetB) hx
  exact And.intro hxA hxB

theorem Topology.closure_diff_subset_closure_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure ((A \ B) : Set X) ⊆ closure (A : Set X) := by
  -- Since `A \ B ⊆ A`, monotonicity of `closure` yields the desired inclusion.
  exact closure_mono (by
    intro x hx
    exact hx.1)

theorem Topology.closure_eq_univ_iff_forall_mem {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = (Set.univ : Set X) ↔ ∀ x : X, x ∈ closure (A : Set X) := by
  constructor
  · intro h x
    have : (x : X) ∈ (Set.univ : Set X) := by
      simp
    simpa [h] using this
  · intro h
    apply Set.Subset.antisymm
    · exact Set.subset_univ _
    · intro x _
      exact h x

theorem Topology.P1_of_subset_within_closureInterior {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP1 : Topology.P1 (X := X) A) (hAB : (A : Set X) ⊆ B)
    (hBsubset : B ⊆ closure (interior A)) :
    Topology.P1 (X := X) B := by
  dsimp [Topology.P1] at hP1 ⊢
  intro x hxB
  -- Step 1: place `x` in `closure (interior A)` using `hBsubset`.
  have hx_clA : (x : X) ∈ closure (interior A) := hBsubset hxB
  -- Step 2: upgrade to `closure (interior B)` via monotonicity.
  have h_int_subset : interior A ⊆ interior B :=
    interior_mono hAB
  have h_cl_subset : closure (interior A) ⊆ closure (interior B) :=
    closure_mono h_int_subset
  exact h_cl_subset hx_clA

theorem Topology.interior_closure_iterate_fourteen_eq_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure
      (interior (closure
        (interior (closure
          (interior (closure
            (interior (closure
              (interior (closure
                (interior (closure
                  (interior (closure
                    (interior (closure
                      (interior (closure
                        (interior (closure (A : Set X))))
                      ))
                    ))
                  ))
                ))
              ))
            ))
          ))
        ))
      )) =
      interior (closure A) := by
  -- Collapse the innermost thirteen‐layer expression.
  have h :=
    Topology.interior_closure_iterate_thirteen_eq_interior_closure
      (X := X) (A := A)
  -- Rewrite using `h`, then simplify via the two‐layer idempotency lemma.
  simpa [h,
    Topology.interior_closure_interior_closure_eq_interior_closure
      (X := X) (A := A)]

theorem Topology.isClosed_boundaryInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (closure (interior (A : Set X)) \ interior A) := by
  -- `closure (interior A)` is closed.
  have h_closed_closure : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  -- The complement of the open set `interior A` is closed.
  have h_closed_compl : IsClosed ((interior (A : Set X))ᶜ) :=
    (isOpen_interior : IsOpen (interior (A : Set X))).isClosed_compl
  -- The desired set is the intersection of two closed sets.
  simpa [Set.diff_eq] using h_closed_closure.inter h_closed_compl

theorem Topology.interior_closure_eq_univ_iff_closure_eq_univ {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) = (Set.univ : Set X) ↔
      closure (A : Set X) = (Set.univ : Set X) := by
  constructor
  · intro hInt
    apply Set.Subset.antisymm
    · exact Set.subset_univ _
    · intro x _
      -- Since `interior (closure A) = univ`, every point belongs to it,
      -- hence to `closure A`.
      have : (x : X) ∈ interior (closure (A : Set X)) := by
        simpa [hInt]
      exact interior_subset this
  · intro hCl
    -- Rewrite using `hCl` and simplify with `interior_univ`.
    simpa [hCl, interior_univ]

theorem Topology.closure_eq_closureInterior_and_P3_implies_P2 {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = closure (interior A) →
      Topology.P3 (X:=X) A → Topology.P2 (X:=X) A := by
  intro h_eq hP3
  have h_pair :
      closure (A : Set X) = closure (interior A) ∧ Topology.P3 (X:=X) A :=
    ⟨h_eq, hP3⟩
  exact
    (Topology.P2_iff_closure_eq_closureInterior_and_P3 (X := X) (A := A)).2 h_pair

theorem Topology.dense_implies_emptyInterior_compl {X : Type*} [TopologicalSpace X]
    {A : Set X} (hDense : Dense (A : Set X)) :
    interior ((A : Set X)ᶜ) = (∅ : Set X) := by
  classical
  -- First, show that `interior (Aᶜ)` is contained in `∅`.
  have h_subset : interior ((A : Set X)ᶜ) ⊆ (∅ : Set X) := by
    intro x hx_int
    -- `x` lies in the closure of `A` because `A` is dense.
    have hx_closure : (x : X) ∈ closure (A : Set X) := by
      have h_cl_eq : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
      simpa [h_cl_eq] using (by simp : (x : X) ∈ (Set.univ : Set X))
    -- Apply the characterization of closure to the open set `interior (Aᶜ)`.
    have h_nonempty :=
      (mem_closure_iff).1 hx_closure
        (interior ((A : Set X)ᶜ)) isOpen_interior hx_int
    -- Derive a contradiction: the intersection is empty.
    rcases h_nonempty with ⟨y, ⟨hy_int_comp, hy_inA⟩⟩
    have hy_notA : (y : X) ∉ A := by
      -- Points in `interior (Aᶜ)` lie in `Aᶜ`.
      have : (y : X) ∈ ((A : Set X)ᶜ) :=
        (interior_subset : interior ((A : Set X)ᶜ) ⊆ (A : Set X)ᶜ) hy_int_comp
      simpa using this
    exact False.elim (hy_notA hy_inA)
  -- Conclude that the two sets are equal.
  exact Set.Subset.antisymm h_subset (Set.empty_subset _)

theorem Topology.closure_interior_union_eq_closure_of_isOpen {X : Type*}
    [TopologicalSpace X] {A B : Set X} (hA_open : IsOpen (A : Set X))
    (hB_open : IsOpen (B : Set X)) :
    closure (interior ((A ∪ B) : Set X)) = closure (A ∪ B) := by
  have h_open : IsOpen ((A ∪ B) : Set X) := hA_open.union hB_open
  simpa [h_open.interior_eq]



theorem Topology.closure_interior_union_interior_subset_closure_interior_union {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure ((interior (A : Set X)) ∪ interior B) ⊆
      closure (interior (A ∪ B)) := by
  -- First, establish the basic inclusion on the non-closed level.
  have h_subset :
      (interior (A : Set X) ∪ interior B : Set X) ⊆ interior (A ∪ B) := by
    intro x hx
    cases hx with
    | inl hA =>
        exact
          (Topology.interior_subset_interior_union_left
            (X := X) (A := A) (B := B)) hA
    | inr hB =>
        exact
          (Topology.interior_subset_interior_union_right
            (X := X) (A := A) (B := B)) hB
  -- Taking closures preserves inclusions.
  exact closure_mono h_subset

set_option maxRecDepth 10000

theorem Topology.interior_subset_closure_interior_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A : Set X) ⊆ closure (interior (A ∪ B)) := by
  intro x hx
  -- `interior A` is contained in `interior (A ∪ B)` because `A ⊆ A ∪ B`.
  have h_int_subset : interior (A : Set X) ⊆ interior (A ∪ B) :=
    interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
  -- Therefore, `x` belongs to `interior (A ∪ B)`.
  have hx' : (x : X) ∈ interior (A ∪ B) := h_int_subset hx
  -- Every point of a set lies in its closure.
  exact subset_closure hx'

theorem Topology.nonempty_interior_closure_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (X:=X) A) (hA : (A : Set X).Nonempty) :
    (interior (closure (A : Set X))).Nonempty := by
  rcases hA with ⟨x, hx⟩
  exact ⟨x, hP3 hx⟩

theorem Topology.interior_closure_iterate_fifteen_eq_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure
      (interior (closure
        (interior (closure
          (interior (closure
            (interior (closure
              (interior (closure
                (interior (closure
                  (interior (closure
                    (interior (closure
                      (interior (closure
                        (interior (closure (A : Set X))))
                      ))
                    ))
                  ))
                ))
              ))
            ))
          ))
        ))
      )) =
      interior (closure A) := by
  -- Collapse the innermost fourteen-layer expression using the existing lemma.
  have h :=
    Topology.interior_closure_iterate_fourteen_eq_interior_closure (X := X) (A := A)
  -- Rewrite and finish with the two-layer idempotency lemma.
  simpa [h,
    Topology.interior_closure_interior_closure_eq_interior_closure
      (X := X) (A := A)]

theorem Set.compl_compl {α : Type*} (s : Set α) : sᶜᶜ = s := by
  ext x
  simp

theorem Topology.closure_union_closure_compl {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) ∪ closure (Aᶜ : Set X) = (Set.univ : Set X) := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    by_cases hx : x ∈ closure (A : Set X)
    · exact Or.inl hx
    · -- Otherwise, `x` is outside `closure A`; in particular, it is outside `A`.
      have hxAcomp : (x : X) ∈ (Aᶜ : Set X) := by
        have : x ∉ (A : Set X) := by
          intro hxA
          have : (x : X) ∈ closure (A : Set X) := subset_closure hxA
          exact hx this
        simpa using this
      exact Or.inr (subset_closure hxAcomp)

theorem Topology.P2_of_boundary_empty {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_boundary : closure (A : Set X) \ interior A = (∅ : Set X)) :
    Topology.P2 (X := X) A := by
  -- From the vanishing boundary we obtain that `A` is both open and closed.
  have h_clopen : IsOpen (A : Set X) ∧ IsClosed (A : Set X) :=
    (Topology.boundary_empty_iff_isClopen (X := X) (A := A)).1 h_boundary
  -- Any open set satisfies `P2`.
  exact isOpen_implies_P2 (X := X) (A := A) h_clopen.1

theorem Topology.boundary_eq_closure_inter_closureCompl {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (A : Set X) \ interior A =
      closure (A : Set X) ∩ closure (Aᶜ : Set X) := by
  -- Relate `closure (Aᶜ)` to the complement of `interior A`.
  have h :
      closure (Aᶜ : Set X) = (interior (A : Set X))ᶜ :=
    Topology.closure_compl_eq_compl_interior (X := X) (A := A)
  -- Rewrite the boundary in two steps.
  calc
    closure (A : Set X) \ interior A
        = closure (A : Set X) ∩ (interior (A : Set X))ᶜ := by
          simpa [Set.diff_eq]
    _ = closure (A : Set X) ∩ closure (Aᶜ : Set X) := by
          simpa [h]

theorem Topology.boundary_compl_eq_boundary {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure ((A : Set X)ᶜ) \ interior (Aᶜ) = closure (A : Set X) \ interior A := by
  -- Express `closure (Aᶜ)` and `interior (Aᶜ)` via complements.
  have h₁ : closure ((A : Set X)ᶜ) = (interior (A : Set X))ᶜ :=
    Topology.closure_compl_eq_compl_interior (X := X) (A := A)
  have h₂ : interior ((A : Set X)ᶜ) = (closure (A : Set X))ᶜ :=
    Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  -- Substitute and simplify.
  simp [h₁, h₂, Set.diff_eq, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc]

theorem Topology.closure_closure_interior_eq_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (closure (interior (A : Set X))) = closure (interior A) := by
  simpa [closure_closure]

theorem Topology.boundary_empty_implies_all_P {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_boundary : closure (A : Set X) \ interior A = (∅ : Set X)) :
    Topology.P1 (X:=X) A ∧ Topology.P2 (X:=X) A ∧ Topology.P3 (X:=X) A := by
  -- From the empty boundary, we learn that `A` is both open and closed.
  have h_clopen : IsOpen (A : Set X) ∧ IsClosed (A : Set X) :=
    (Topology.boundary_empty_iff_isClopen (X := X) (A := A)).1 h_boundary
  -- Any open set satisfies all three properties `P1`, `P2`, and `P3`.
  simpa using
    Topology.isOpen_implies_all_P (X := X) (A := A) h_clopen.1

theorem Topology.boundary_subset_closureCompl {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ interior A ⊆ closure (Aᶜ : Set X) := by
  intro x hx
  -- `hx` provides that `x ∈ closure A` and `x ∉ interior A`.
  have h_not_int : (x : X) ∉ interior (A : Set X) := hx.2
  -- Since `closure (Aᶜ) = (interior A)ᶜ`, the non-membership just obtained
  -- translates into membership of `x` in `closure (Aᶜ)`.
  have h_eq := Topology.closure_compl_eq_compl_interior (X := X) (A := A)
  have : (x : X) ∈ (interior (A : Set X))ᶜ := by
    simpa using h_not_int
  simpa [h_eq] using this

theorem Topology.closure_eq_closureInterior_union_boundary {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) =
      closure (interior A) ∪ (closure (A : Set X) \ interior A) := by
  -- We establish both inclusions and then apply `Subset.antisymm`.
  apply Set.Subset.antisymm
  · -- `closure A ⊆ …`
    intro x hx_clA
    by_cases hx_int : (x : X) ∈ interior A
    · -- If `x ∈ interior A`, then `x ∈ closure (interior A)`.
      have : (x : X) ∈ closure (interior A) := subset_closure hx_int
      exact Or.inl this
    · -- Otherwise `x ∈ closure A \ interior A`.
      exact Or.inr ⟨hx_clA, hx_int⟩
  · -- The reverse inclusion is straightforward since both summands lie in `closure A`.
    intro x hx
    cases hx with
    | inl hx_clIntA =>
        -- `closure (interior A) ⊆ closure A`
        exact (closure_mono (interior_subset : interior A ⊆ A)) hx_clIntA
    | inr hx_boundary =>
        -- The boundary is defined using `closure A`.
        exact hx_boundary.1

theorem Topology.boundary_closure_subset_boundary {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (closure (A : Set X) \ interior (closure (A : Set X))) ⊆
      (closure (A : Set X) \ interior A) := by
  intro x hx
  rcases hx with ⟨hx_cl, hx_not_int_cl⟩
  have hx_not_intA : (x : X) ∉ interior (A : Set X) := by
    intro hx_intA
    have : (x : X) ∈ interior (closure (A : Set X)) :=
      (Topology.interior_subset_interior_closure (X := X) (A := A)) hx_intA
    exact hx_not_int_cl this
  exact And.intro hx_cl hx_not_intA

theorem Topology.boundaryInterior_subset_boundary {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (closure (interior (A : Set X)) \ interior A) ⊆
      closure (A : Set X) \ interior A := by
  intro x hx
  rcases hx with ⟨hx_cl, hx_not_int⟩
  -- Since `interior A ⊆ A`, taking closures yields
  -- `closure (interior A) ⊆ closure A`.
  have h_subset :
      closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  -- Transport `x ∈ closure (interior A)` along this inclusion.
  have hx_clA : (x : X) ∈ closure (A : Set X) := h_subset hx_cl
  exact ⟨hx_clA, hx_not_int⟩

theorem Topology.denseInterior_iff_interior_closure_interior_eq_univ {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) ↔
      interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
  constructor
  ·
    intro hDense
    exact
      Topology.denseInterior_implies_interior_closure_interior_eq_univ
        (X := X) (A := A) hDense
  ·
    intro hIntEq
    -- Show that `closure (interior A)` equals the whole space.
    have h_closure :
        closure (interior (A : Set X)) = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · exact Set.subset_univ _
      ·
        intro x _
        -- Since `interior (closure (interior A)) = univ`, every `x`
        -- lies in this interior, hence in the corresponding closure.
        have hx_int :
            (x : X) ∈ interior (closure (interior (A : Set X))) := by
          simpa [hIntEq]
        exact
          (interior_subset :
            interior (closure (interior (A : Set X))) ⊆
              closure (interior (A : Set X))) hx_int
    -- Conclude density from the closure equality.
    simpa [Dense, h_closure]

theorem Topology.closure_union_closure_subset_closure_union {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) ∪ closure B ⊆ closure (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      have h_subset : closure (A : Set X) ⊆ closure (A ∪ B) :=
        Topology.closure_subset_closure_union_left (X := X) (A := A) (B := B)
      exact h_subset hA
  | inr hB =>
      have h_subset : closure (B : Set X) ⊆ closure (A ∪ B) :=
        Topology.closure_subset_closure_union_right (X := X) (A := A) (B := B)
      exact h_subset hB

theorem Topology.boundary_eq_univ_of_dense_and_emptyInterior {X : Type*}
    [TopologicalSpace X] {A : Set X} (hDense : Dense (A : Set X))
    (hInt : interior (A : Set X) = (∅ : Set X)) :
    closure (A : Set X) \ interior A = (Set.univ : Set X) := by
  -- The density of `A` says that `closure A = univ`.
  have h_cl : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  -- Substitute both equalities and simplify.
  simpa [h_cl, hInt]

theorem Topology.isClosed_interior_iff_closureInterior_eq_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    IsClosed (interior (A : Set X)) ↔
      closure (interior (A : Set X)) = interior A := by
  constructor
  · intro hClosed
    simpa using hClosed.closure_eq
  · intro hEq
    have hClosed : IsClosed (closure (interior (A : Set X))) :=
      isClosed_closure
    simpa [hEq] using hClosed

theorem Topology.interior_closure_iterate_sixteen_eq_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure
      (interior (closure
        (interior (closure
          (interior (closure
            (interior (closure
              (interior (closure
                (interior (closure
                  (interior (closure
                    (interior (closure
                      (interior (closure
                        (interior (closure
                          (interior (closure (A : Set X))))
                        ))
                      ))
                    ))
                  ))
                ))
              ))
            ))
          ))
        ))
      )) =
      interior (closure A) := by
  -- Collapse the innermost fifteen‐layer expression using the existing lemma.
  have h :=
    Topology.interior_closure_iterate_fifteen_eq_interior_closure
      (X := X) (A := A)
  -- Rewrite and finish with the two‐layer idempotency lemma.
  simpa [h,
        Topology.interior_closure_interior_closure_eq_interior_closure
          (X := X) (A := A)]

theorem Topology.interior_inter_interior_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior ((A ∩ interior (B : Set X)) : Set X) = interior A ∩ interior B := by
  -- `interior B` is an open set.
  have h_open : IsOpen (interior (B : Set X)) := isOpen_interior
  -- Apply the general lemma for the intersection with an open set.
  simpa using
    Topology.interior_inter_open_right
      (X := X) (A := A) (B := interior (B : Set X)) h_open

theorem Topology.isOpen_iff_interior_eq {X : Type*} [TopologicalSpace X] {U : Set X} :
    IsOpen (U : Set X) ↔ interior U = U := by
  constructor
  · intro hU
    simpa using hU.interior_eq
  · intro h_eq
    have h_open : IsOpen (interior (U : Set X)) := isOpen_interior
    simpa [h_eq] using h_open



theorem Topology.closureInterior_eq_univ_of_P2_and_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 (X := X) A) (hDense : Dense (A : Set X)) :
    closure (interior (A : Set X)) = (Set.univ : Set X) := by
  -- From `P2` we have equality of the two closures.
  have h_eq : closure (A : Set X) = closure (interior A) :=
    Topology.P2_implies_closure_eq_closureInterior (X := X) (A := A) hP2
  -- Density of `A` tells us its closure is the whole space.
  have h_closureA : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  -- Combine the two equalities.
  simpa [h_closureA] using h_eq.symm

theorem Topology.P1_of_boundary_subset_closureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X}
    (h_boundary : (closure (A : Set X) \ interior A) ⊆ closure (interior A)) :
    Topology.P1 (X := X) A := by
  exact
    (Topology.P1_iff_boundary_subset_closureInterior (X := X) (A := A)).2
      h_boundary

theorem Topology.boundary_empty_of_closed_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} (h_closed : IsClosed (A : Set X)) (h_dense : Dense (A : Set X)) :
    closure (A : Set X) \ interior A = (∅ : Set X) := by
  -- A closed and dense set is the whole space.
  have h_eq_univ : (A : Set X) = (Set.univ : Set X) :=
    Topology.closed_dense_eq_univ (X := X) (A := A) h_closed h_dense
  -- Rewrite both the closure and the interior using `h_eq_univ`.
  have h_closure_eq : closure (A : Set X) = (Set.univ : Set X) := by
    simpa [h_eq_univ, closure_univ] using (h_closed.closure_eq)
  have h_interior_eq : interior (A : Set X) = (Set.univ : Set X) := by
    simpa [h_eq_univ, interior_univ] using
      (isOpen_univ.interior_eq.symm.trans (by simp [h_eq_univ]))
  -- Compute the boundary using these equalities.
  simpa [h_closure_eq, h_interior_eq, Set.diff_self]

theorem Topology.closure_inter_interiorCompl_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (A : Set X) ∩ interior ((A : Set X)ᶜ) = (∅ : Set X) := by
  ext x
  constructor
  · intro hx
    have hFalse : False := by
      rcases hx with ⟨h_clA, h_intCompl⟩
      -- Using the neighbourhood characterization of the closure,
      -- obtain a point of `A` inside `interior (Aᶜ)`, which is impossible.
      have h_nonempty :
          ((interior ((A : Set X)ᶜ)) ∩ (A : Set X)).Nonempty := by
        have h := (mem_closure_iff).1 h_clA
        have := h (interior ((A : Set X)ᶜ)) isOpen_interior h_intCompl
        -- Rearrange intersections to the required form.
        simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using this
      rcases h_nonempty with ⟨y, ⟨hy_intCompl, hyA⟩⟩
      -- The point `y` lies in both `A` and `Aᶜ`, a contradiction.
      have hy_notA : (y : X) ∈ (A : Set X)ᶜ :=
        (interior_subset : interior ((A : Set X)ᶜ) ⊆ (A : Set X)ᶜ) hy_intCompl
      exact hy_notA hyA
    exact hFalse.elim
  · intro hx
    cases hx

theorem Topology.boundary_eq_univ_diff_interior_of_dense {X : Type*}
    [TopologicalSpace X] {A : Set X} (hDense : Dense (A : Set X)) :
    closure (A : Set X) \ interior A = (Set.univ : Set X) \ interior A := by
  simpa [hDense.closure_eq]

theorem Topology.boundary_subset_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    closure (A : Set X) \ interior A ⊆ (A : Set X) := by
  intro x hx
  have hx_cl : (x : X) ∈ closure (A : Set X) := hx.1
  simpa [hA_closed.closure_eq] using hx_cl