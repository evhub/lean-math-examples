namespace ctx
    @[inline, reducible] def pipe {A B: Sort _} (a: A) (f: A → B): B := f a
    infix ` ↦ `:50 := pipe

    def of {A X: Sort _} (a: A): (A → X) → X :=
        λ xa: A → X,
        xa a

    def of_func {A B X: Sort _} (f: A → B): A → (B → X) → X :=
        λ a: A,
        λ ctx: B → X,
        a ↦ f ↦ ctx

    def uncurry {A B X: Sort _} (fx: ((A → B) → X) → X): A → (B → X) → X :=
        begin
            intros a xb,
            apply fx,
            intro f,
            apply xb,
            apply f,
            exact a,
        end

    def curry.of_dne {A B C X: Sort _} (bdne: ((B → X) → X) → C) (fx: A → (B → X) → X): ((A → C) → X) → X :=
        begin
            intro xf,
            apply xf,
            intro a,
            let bxx: (B → X) → X := fx a,
            apply bdne,
            exact bxx,
        end

    def dne {A X: Sort _} (xxa: (A → X) → X) (ctx: A → X): X :=
        xxa ctx

    inductive or (A: Sort _) (B: Sort _)
    | inl (a: A) : or
    | inr (b: B) : or

    def or.of_sum {A B: Sort _} (ab: A ⊕ B): or A B :=
        begin
            cases ab,
            case sum.inl {
                apply or.inl,
                assumption,
            },
            case sum.inr {
                apply or.inr,
                assumption,
            },
        end

    def lem {A X: Sort _} (ctx: (or A (A → X)) → X): X :=
        begin
            apply ctx,
            apply or.inr,
            intro a,
            apply ctx,
            apply or.inl,
            exact a,
        end

    theorem lem.of_prop {X: Sort _} {P: Prop} (ctx: P ∨ (P → X) → X): X :=
        begin
            apply ctx,
            right,
            intro p,
            apply ctx,
            left,
            exact p,
        end

    def of_not {A X: Sort _} (na: A → false): A → X :=
        begin
            intro a,
            apply false.elim,
            apply na,
            exact a,
        end

    theorem of_not.of_prop {X: Sort _} {P: Prop} (np: ¬P): P → X :=
        of_not np

    def inner_to_not {A X: Sort _} (xxa: (A → X) → X): (A → false) → X :=
        λ na: A → false,
        let f: A → X := of_not na in
        xxa f

    theorem inner_to_not.of_prop {X: Sort _} {P: Prop} (xxp: (P → X) → X): ¬P → X :=
        inner_to_not xxp

    namespace fixed_output
        constant X: Sort _
        axiom to_not {A: Sort _}: (A → X) → (A → false)

        theorem to_not.of_prop {P: Prop} (xp: P → X): ¬P :=
            to_not xp

        def to_double_neg {A: Sort _} (xxa: (A → X) → X): (A → false) → false :=
            xxa ↦ inner_to_not ↦ to_not

        noncomputable def of_double_neg {A: Sort _} (nna: (A → false) → false): (A → X) → X :=
            λ xa: A → X,
            let na: A → false := to_not xa in
            let bot: false := nna na in
            false.elim bot
    end fixed_output
end ctx
