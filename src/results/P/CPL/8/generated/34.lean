

theorem P1_complement_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P1 (Aᶜ) := by
  intro hClosed
  have hOpen : IsOpen (Aᶜ : Set X) := hClosed.isOpen_compl
  exact P1_of_open (A := Aᶜ) hOpen

theorem P3_preimage_open {X : Type*} [TopologicalSpace X] {A B : Set X} : IsOpen B → P3 A → P3 (A ∩ B) := by
  intro hBOpen hP3
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- `x` is in the interior of `closure A`
  have hxInt : x ∈ interior (closure A) := hP3 hxA
  -- Auxiliary open neighbourhood around `x`
  set O : Set X := interior (closure A) ∩ B with hOdef
  have hOopen : IsOpen O := by
    have : IsOpen (interior (closure A)) := isOpen_interior
    simpa [hOdef] using this.inter hBOpen
  have hxO : x ∈ O := by
    dsimp [O, hOdef]
    exact ⟨hxInt, hxB⟩
  -- `O` is contained in the closure of `A ∩ B`
  have hOsubset : (O : Set X) ⊆ closure (A ∩ B) := by
    intro y hyO
    rcases hyO with ⟨hyInt, hyB⟩
    have hyClA : y ∈ closure (A : Set X) := interior_subset hyInt
    -- Show `y ∈ closure (A ∩ B)`
    have : y ∈ closure (A ∩ B) := by
      refine (mem_closure_iff).2 ?_
      intro U hUopen hyU
      have hVopen : IsOpen (U ∩ B) := hUopen.inter hBOpen
      have hyV : y ∈ U ∩ B := ⟨hyU, hyB⟩
      have hNonempty : ((U ∩ B) ∩ A).Nonempty :=
        (mem_closure_iff).1 hyClA (U ∩ B) hVopen hyV
      rcases hNonempty with ⟨z, ⟨⟨hzU, hzB⟩, hzA⟩⟩
      exact ⟨z, hzU, ⟨hzA, hzB⟩⟩
    exact this
  -- Use `O` to witness membership in the required interior
  have hNhd : (O : Set X) ∈ 𝓝 x := hOopen.mem_nhds hxO
  have hMem : x ∈ interior (closure (A ∩ B)) :=
    (mem_interior_iff_mem_nhds).2 (Filter.mem_of_superset hNhd hOsubset)
  simpa using hMem

theorem P3_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (interior (closure A)) := by
  exact P3_of_open (A := interior (closure A)) isOpen_interior