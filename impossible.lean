import .posets

namespace impossible
    open nat

    open posets


    -- bool:
    instance bool_order:
        bot_order bool := {
            le := λ x y: bool, x = ff ∨ (x = tt ∧ y = tt),
            le_refl := begin
                intros,
                induction a;
                simp,
            end,
            le_trans := begin
                intros,
                induction a_1,
                case or.inl {
                    simp,
                    left,
                    assumption,
                },
                case or.inr {
                    simp,
                    simp at a_2,
                    cases a_2,
                    case or.inl {
                        induction b,
                        case bool.ff {
                            apply false.elim,
                            apply ff_eq_tt_eq_false,
                            apply a_1.2,
                        },
                        case bool.tt {
                            apply false.elim,
                            apply tt_eq_ff_eq_false,
                            assumption,
                        },
                    },
                    case or.inr {
                        right,
                        split,
                        apply a_1.1,
                        apply a_2.2,
                    },
                },
            end,
            le_antisymm := begin
                intros,
                cases a_1,
                case or.inl {
                    cases a_2,
                    case or.inl {
                        rw [a_1, a_2],
                    },
                    case or.inr {
                        apply false.elim,
                        apply ff_eq_tt_eq_false,
                        rw [←a_1, ←a_2.2],
                    },
                },
                case or.inr {
                    cases a_2,
                    case or.inl {
                        apply false.elim,
                        apply ff_eq_tt_eq_false,
                        rw [←a_1.2, a_2],
                    },
                    case or.inr {
                        rw [a_1.1, a_2.1],
                    },
                },
            end,
            bot := ff,
            bot_le := begin
                intros,
                left,
                refl,
            end,
        }

    @[reducible, pattern] instance bool.has_zero:
        has_zero bool :=
            (| ff |)

    @[reducible, pattern] instance bool.has_one:
        has_one bool :=
            (| tt |)

    theorem bool.le_tt (x: bool):
        x ≤ 1 := begin
            induction x,
            apply bot_le,
            refl,
        end

    instance bool.coe_to_nat:
        has_coe bool nat := {
            coe := λ x: bool, match x with
                | 0 := 0
                | 1 := 1
                end,
        }


    -- bitstream:
    structure bitstream :=
        (bit: ℕ → bool)

    instance bitstream.coe_to_fun:
        has_coe_to_fun bitstream := {
            F := λ b: bitstream, ℕ → bool,
            coe := bitstream.bit,
        }

    @[simp] theorem bitstream.bit.of_coe (b: bitstream) (n: ℕ):
        b n = b.bit n := rfl

    def bitstream.cons (x: bool) (b: bitstream): bitstream := {
        bit := λ n: ℕ, match n with
            | 0 := x
            | (succ m) := b m
            end,
    }

    infixr ` # `:67 := bitstream.cons

    def all (x: bool): bitstream := {
        bit := λ n, x,
    }

    @[simp] theorem all.of_bit (x: bool) (n: ℕ):
        (all x) n = x := rfl


    -- find:
    def findN: ℕ → (bitstream → bool) → bitstream
    | 0 P := all 0
    | (succ N) P :=
        let find0 := 0 # findN N (λ b, P (0 # b)) in
        let find1 := 1 # findN N (λ b, P (1 # b)) in
        match P find0 with
        | tt := find0
        | ff := find1
        end

    def find (P: bitstream → bool): bitstream := {
        bit := λ n: ℕ, (findN (succ n) P) n,
    }

    def forsome (P: bitstream → bool): bool :=
        P (find P)

    def forevery (P: bitstream → bool): bool :=
        bnot (forsome (bnot ∘ P))

    def equal {T: Sort _} [decidable_eq T] (P1 P2: bitstream → T): bool :=
        forevery (λ b: bitstream, P1 b = P2 b)


    -- tests:
    namespace find_test
        def f (b: bitstream): ℤ :=
            b (7 * (b 4) + 4 * (b 7) + 4)

        def g (b: bitstream): ℤ :=
            b ((b 4) + 11 * (b 7))

        def h (b: bitstream): ℤ :=
            if b 7 = 0 then
                if b 4 = 0 then
                    b 4
                else
                    b 11
            else
                if b 4 = 1 then
                    b 15
                else
                    b 8

        #eval equal f g
        #eval equal f h
        #eval equal g h
        #eval equal f f
        #eval equal g g
        #eval equal h h
    end find_test


    -- conat:
    structure conat extends bitstream :=
        [mono: monotone.decreasing bit]

    instance conat.coe_to_fun:
        has_coe_to_fun conat := {
            F := λ cn: conat, ℕ → bool,
            coe := λ cn: conat, cn.bit,
        }

    @[simp] theorem conat.bit.of_coe (cn: conat) (n: ℕ):
        cn n = cn.bit n := rfl

    def conat.zero: conat := {
        bit := all 0,
        mono := begin
            split,
            intros,
            refl,
        end,
    }

    instance conat.has_zero:
        has_zero conat :=
            (| conat.zero |)

    def conat.inf: conat := {
        bit := all 1,
        mono := begin
            split,
            intros,
            refl,
        end,
    }

    def conat.succ (cn: conat): conat := {
        bit := λ n: ℕ, match n with
            | 0 := 1
            | (succ m) := cn m
            end,
        mono := begin
            split,
            intros,
            simp,
            induction x,
            case nat.zero {
                rw [conat.succ._match_1],
                apply bool.le_tt,
            },
            case nat.succ {
                induction y,
                case nat.zero {
                    apply false.elim,
                    apply not_succ_le_zero x_n a,
                },
                case nat.succ {
                    rw [conat.succ._match_1, conat.succ._match_1],
                    apply cn.mono.elim,
                    apply le_of_succ_le_succ,
                    assumption,
                },
            },
        end,
    }
end impossible
