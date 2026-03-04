# Lean4 완전 정복 가이드 —  Part 14-A: 부울 대수 기초 — 부울 연산, 부울 함수, 부울 식

> **Rosen 이산수학 8판 · Chapter 12 (Section 12.1) 기반**
> **『Mathematics in Lean』 + Lean 4 공식화**

---

## 0. 들어가며: 이 파트에서 배울 것

컴퓨터는 근본적으로 **0과 1**, 두 가지 상태만을 다루는 기계이다. 스위치가 켜지거나(1) 꺼지거나(0), 전류가 흐르거나(1) 안 흐르거나(0) — 이것이 전부이다. 이런 0과 1의 세계를 수학적으로 다루는 도구가 바로 **부울 대수**(Boolean Algebra)이다.

1854년 조지 부울(George Boole)이 "사고의 법칙(The Laws of Thought)"에서 처음 제시한 논리 규칙을, 1938년 클로드 섀넌(Claude Shannon)이 회로 설계에 사용할 수 있음을 증명하였다. 이것이 현대 컴퓨터의 기초가 되었다.

이 파트에서 다루는 내용:

1. **부울 보수**(complement): $\overline{0} = 1$, $\overline{1} = 0$ — "반대로 뒤집기"
2. **부울 합**(Boolean sum / OR): $+$ — "둘 중 하나라도 1이면 1"
3. **부울 곱**(Boolean product / AND): $\cdot$ — "둘 다 1이어야 1"
4. **부울 변수**(Boolean variable)와 **부울 함수**(Boolean function)
5. **부울 식**(Boolean expression)의 재귀적 정의
6. Lean 4에서 `Bool`, `Prop`, `BooleanAlgebra` 타입클래스
7. 논리 연산과 부울 연산의 대응 관계

> 💡 **선수 지식**: Part 1~3 정도의 Lean 4 기초 (타입, 함수, 명제와 증명의 개념)만 있으면 충분하다.

---

## 1. 부울 대수란 무엇인가? — 0과 1의 수학

### 1.1 일상 속의 부울 대수

부울 대수를 어렵게 생각할 필요가 전혀 없다. 일상에서 이미 매일 사용하고 있기 때문이다:

| 일상 표현 | 부울 대수 |
|----------|----------|
| 스위치가 **켜짐** / **꺼짐** | 1 / 0 |
| 참(**True**) / 거짓(**False**) | 1 / 0 |
| 예(**Yes**) / 아니오(**No**) | 1 / 0 |
| 전류가 **흐름** / **안 흐름** | 1 / 0 |

부울 대수는 집합 $B = \{0, 1\}$ 위에서 정의된 연산과 규칙의 체계이다. 가능한 값은 오직 **0**과 **1** 뿐이다. "2"나 "0.5" 같은 건 없다!

### 1.2 세 가지 기본 연산

부울 대수에서 가장 많이 사용되는 세 가지 연산이 있다.

#### (1) **보수화**(complementation) — "반대로 뒤집기"

**보수**(complement)는 0과 1을 뒤집는 연산이다. 기호로는 $\overline{x}$ 또는 $\lnot x$로 쓴다.

$$\overline{0} = 1, \quad \overline{1} = 0$$

> 🔦 **비유**: 방의 불이 켜져 있으면(1) 스위치를 누르면 꺼지고(0), 꺼져 있으면(0) 스위치를 누르면 켜진다(1). 보수는 바로 이 "스위치 누르기"이다.

Lean 4에서는 `!` (not) 또는 `Bool.not`으로 표현한다:

```lean
#eval !true   -- false
#eval !false  -- true
```

논리학의 **부정**(negation, ¬)과 정확히 대응한다.

#### (2) **부울 합**(Boolean sum / OR) — "둘 중 하나라도 1이면 1"

기호는 $+$ 또는 $\lor$(OR)이다. 진리표는:

| $x$ | $y$ | $x + y$ |
|-----|-----|---------|
| 1   | 1   | **1**   |
| 1   | 0   | **1**   |
| 0   | 1   | **1**   |
| 0   | 0   | **0**   |

> 🍕 **비유**: "피자를 시키거나($x$) 치킨을 시키거나($y$) — 둘 중 하나라도 시키면 저녁을 먹을 수 있다(1). 둘 다 안 시키면 굶는다(0)." 이것이 OR이다.

핵심: $1 + 1 = 1$이다! 일반 수학의 덧셈과 다르다. 부울 합에서는 "이미 1이면, 더 해봐야 1"이다.

Lean 4에서는 `||` (or) 또는 `Bool.or`로 표현한다:

```lean
#eval (true || true)    -- true   (1 + 1 = 1)
#eval (true || false)   -- true   (1 + 0 = 1)
#eval (false || true)   -- true   (0 + 1 = 1)
#eval (false || false)  -- false  (0 + 0 = 0)
```

논리학의 **논리합**(disjunction, ∨)과 대응한다.

#### (3) **부울 곱**(Boolean product / AND) — "둘 다 1이어야 1"

기호는 $\cdot$ 또는 $\land$(AND)이다. 혼돈이 없을 때 $\cdot$는 생략하기도 한다 (일반 수학처럼).

| $x$ | $y$ | $x \cdot y$ |
|-----|-----|-------------|
| 1   | 1   | **1**       |
| 1   | 0   | **0**       |
| 0   | 1   | **0**       |
| 0   | 0   | **0**       |

> 🔑 **비유**: "열쇠($x$)도 있고 비밀번호($y$)도 맞아야 금고가 열린다(1). 하나라도 없으면 못 연다(0)." 이것이 AND이다.

Lean 4에서는 `&&` (and) 또는 `Bool.and`로 표현한다:

```lean
#eval (true && true)    -- true   (1 · 1 = 1)
#eval (true && false)   -- false  (1 · 0 = 0)
#eval (false && true)   -- false  (0 · 1 = 0)
#eval (false && false)  -- false  (0 · 0 = 0)
```

논리학의 **논리곱**(conjunction, ∧)과 대응한다.

### 1.3 연산 우선순위

괄호를 사용하지 않는 경우, 부울 연산자의 우선순위는:

1. **보수**(complement) — 가장 먼저 계산
2. **부울 곱**(AND) — 그 다음
3. **부울 합**(OR) — 가장 나중에 계산

> 🧮 이것은 일반 수학에서 "괄호 → 거듭제곱 → 곱셈/나눗셈 → 덧셈/뺄셈" 순서와 비슷하다. NOT이 가장 강하고, AND가 곱셈처럼, OR이 덧셈처럼 취급된다.

**예제 1** (Rosen 예제 1): $1 \cdot 0 + \overline{(0+1)}$의 값을 구하라.

풀이를 단계별로 따라가 보자:

1. 먼저 괄호 안: $0 + 1 = 1$ (부울 합)
2. 보수 적용: $\overline{1} = 0$
3. 부울 곱: $1 \cdot 0 = 0$
4. 부울 합: $0 + 0 = 0$

따라서 답은 **0**이다.

```lean
-- Lean 4로 직접 계산해 보자
#eval (true && false) || (!(false || true))
-- = (false) || (!(true))
-- = false || false
-- = false
```

---

## 2. 부울 연산과 논리 연산의 대응 — "같은 것의 다른 이름"

부울 대수와 논리학은 본질적으로 같은 구조를 공유한다. 기호만 다를 뿐이다:

| 부울 대수 | 논리학 | Lean 4 (`Bool`) | Lean 4 (`Prop`) |
|----------|--------|----------------|-----------------|
| 0 | **F**(False) | `false` | `False` |
| 1 | **T**(True) | `true` | `True` |
| $\overline{x}$ (보수) | $\lnot p$ (부정) | `!x` | `¬ p` |
| $x + y$ (부울 합) | $p \lor q$ (논리합) | `x \|\| y` | `p ∨ q` |
| $x \cdot y$ (부울 곱) | $p \land q$ (논리곱) | `x && y` | `p ∧ q` |

> ⚠️ **`Bool`과 `Prop`의 차이**: Lean 4에서 `Bool`은 계산 가능한 참/거짓 값이고, `Prop`은 논리적 명제이다. `Bool`은 `#eval`로 계산할 수 있지만, `Prop`은 **증명**해야 한다. 부울 대수를 다룰 때 둘 다 사용하게 된다.

**예제 2** (Rosen 예제 2): $1 \cdot 0 + \overline{(0+1)} = 0$을 논리식으로 변환하라.

부울식 → 논리식 변환 규칙:
- $1 \to T$, $0 \to F$
- 부울 합($+$) → 논리합($\lor$)
- 부울 곱($\cdot$) → 논리곱($\land$)
- 보수($\overline{\phantom{x}}$) → 부정($\lnot$)

$$1 \cdot 0 + \overline{(0+1)} = 0 \quad\longrightarrow\quad (T \land F) \lor \lnot(T \lor F) \equiv F$$

```lean
-- Lean 4에서 확인
example : (True ∧ False) ∨ ¬(False ∨ True) ↔ False := by
  constructor
  · intro h
    rcases h with ⟨_, hf⟩ | hn
    · exact hf
    · exact hn (Or.inr True.intro)
  · intro h; exact h.elim
```

**예제 3** (Rosen 예제 3): $(T \land T) \lor \lnot F \equiv T$를 부울식으로 변환하라.

$$T \to 1, \; F \to 0 \quad\Longrightarrow\quad (1 \cdot 1) + \overline{0} = 1$$

확인: $(1 \cdot 1) + \overline{0} = 1 + 1 = 1$ ✓

---

## 3. 부울 변수와 부울 함수 — "입력 → 출력"

### 3.1 부울 변수

**부울 변수**(Boolean variable)는 0 또는 1, 오직 두 값만 취할 수 있는 변수이다.

일반 수학에서 $x$가 실수 전체를 돌아다닐 수 있는 것과 달리, 부울 변수 $x$는 **0 아니면 1**이다. 그래서 가능한 경우의 수가 매우 제한적이다.

### 3.2 부울 함수의 정의

$B = \{0, 1\}$이라고 하면:

$$B^n = \{(x_1, x_2, \ldots, x_n) \mid x_i \in B,\; 1 \le i \le n\}$$

이것은 0과 1로 구성된 모든 가능한 $n$**짝**(n-tuple)들의 집합이다. $B^n$에서 $B$로 가는 함수를 **$n$차 부울 함수**(Boolean function of degree $n$)라고 한다.

> 💡 **쉽게 말하면**: $n$개의 0/1 값을 입력받아서, 하나의 0/1 값을 출력하는 함수이다.

**예를 들어** $n = 2$이면:
- 입력 가능한 조합: $(0,0), (0,1), (1,0), (1,1)$ — 총 4가지
- 각 조합에 대해 출력이 0 또는 1

```
입력 (x, y)  →  [ 부울 함수 F ]  →  출력 0 또는 1
```

### 3.3 Lean 4에서 부울 함수 표현

Lean 4에서 부울 함수는 매우 자연스럽게 표현된다:

```lean
-- 2차 부울 함수: Bool × Bool → Bool
def myBoolFunc : Bool → Bool → Bool
  | true,  true  => false
  | true,  false => true
  | false, true  => false
  | false, false => false
```

**예제 4** (Rosen 예제 4): $F(x, y) = x\overline{y}$는 차수가 2인 부울 함수이다.

| $x$ | $y$ | $\overline{y}$ | $x\overline{y}$ |
|-----|-----|-----------------|------------------|
| 1   | 1   | 0               | **0**            |
| 1   | 0   | 1               | **1**            |
| 0   | 1   | 0               | **0**            |
| 0   | 0   | 1               | **0**            |

```lean
-- x · (not y) 를 Lean 4로 표현
def F_ex4 (x y : Bool) : Bool := x && (!y)

#eval F_ex4 true true    -- false  (F(1,1) = 0)
#eval F_ex4 true false   -- true   (F(1,0) = 1)
#eval F_ex4 false true   -- false  (F(0,1) = 0)
#eval F_ex4 false false  -- false  (F(0,0) = 0)
```

**예제 5** (Rosen 예제 5): $F(x, y, z) = xy + \overline{z}$ — 3차 부울 함수

| $x$ | $y$ | $z$ | $xy$ | $\overline{z}$ | $xy + \overline{z}$ |
|-----|-----|-----|------|-----------------|---------------------|
| 1   | 1   | 1   | 1    | 0               | **1** |
| 1   | 1   | 0   | 1    | 1               | **1** |
| 1   | 0   | 1   | 0    | 0               | **0** |
| 1   | 0   | 0   | 0    | 1               | **1** |
| 0   | 1   | 1   | 0    | 0               | **0** |
| 0   | 1   | 0   | 0    | 1               | **1** |
| 0   | 0   | 1   | 0    | 0               | **0** |
| 0   | 0   | 0   | 0    | 1               | **1** |

```lean
def F_ex5 (x y z : Bool) : Bool := (x && y) || (!z)

-- 모든 경우를 확인
#eval F_ex5 true true true    -- true
#eval F_ex5 true true false   -- true
#eval F_ex5 true false true   -- false
#eval F_ex5 true false false  -- true
#eval F_ex5 false true true   -- false
#eval F_ex5 false true false  -- true
#eval F_ex5 false false true  -- false
#eval F_ex5 false false false -- true
```

### 3.4 $n$차 부울 함수는 몇 개 존재하는가?

**예제 7** (Rosen 예제 7):

$n$개의 변수에 대해 $2^n$개의 서로 다른 입력 조합이 있다. 각 조합에 대해 출력이 0 또는 1이므로:

$$\text{n차 부울 함수의 수} = 2^{2^n}$$

| $n$ | 입력 조합 수 ($2^n$) | 부울 함수 수 ($2^{2^n}$) |
|-----|-------------------|----------------------|
| 1   | 2                 | **4** |
| 2   | 4                 | **16** |
| 3   | 8                 | **256** |
| 4   | 16                | **65,536** |
| 5   | 32                | **4,294,967,296** (약 43억) |
| 6   | 64                | 약 $1.8 \times 10^{19}$ |

변수가 조금만 늘어도 가능한 함수의 수가 폭발적으로 증가한다!

```lean
-- Lean 4로 계산
#eval (2 : Nat) ^ (2 ^ 1)   -- 4
#eval (2 : Nat) ^ (2 ^ 2)   -- 16
#eval (2 : Nat) ^ (2 ^ 3)   -- 256
#eval (2 : Nat) ^ (2 ^ 4)   -- 65536
```

---

## 4. 부울 식의 재귀적 정의 — "복잡한 것을 단순한 것으로 쌓기"

**부울 식**(Boolean expression)은 부울 변수와 부울 연산자를 사용해 만든 표현이다. 재귀적으로 정의된다:

**기저 단계**(Base):
- $0$, $1$은 부울 식이다.
- $x_1, x_2, \ldots, x_n$ (부울 변수들)은 부울 식이다.

**재귀 단계**(Recursive): $E_1$과 $E_2$가 부울 식이면:
- $\overline{E_1}$은 부울 식이다. (보수)
- $(E_1 \cdot E_2)$는 부울 식이다. (부울 곱)
- $(E_1 + E_2)$는 부울 식이다. (부울 합)

> 🧱 **비유**: 레고 블록처럼 작은 조각(0, 1, 변수)에서 시작해서, 세 가지 연산(보수, 곱, 합)으로 점점 복잡한 식을 쌓아 올리는 것이다.

### 4.1 Lean 4에서 부울 식을 귀납적 타입으로 표현하기

Lean 4에서는 **귀납적 타입**(inductive type)으로 부울 식의 구조를 정확하게 표현할 수 있다:

```lean
-- 부울 식의 재귀적 정의 (문법 트리)
inductive BoolExpr where
  | lit : Bool → BoolExpr          -- 상수 0, 1
  | var : Nat → BoolExpr           -- 변수 x₁, x₂, ...
  | not : BoolExpr → BoolExpr      -- 보수
  | and : BoolExpr → BoolExpr → BoolExpr  -- 부울 곱
  | or  : BoolExpr → BoolExpr → BoolExpr  -- 부울 합
```

이것은 **추상 구문 트리**(AST)라고도 불리는 것으로, 부울 식의 구조를 나무(tree) 형태로 나타낸다.

예를 들어 $xy + \overline{z}$는:

```
        or
       /   \
     and    not
    /   \    |
  var 0  var 1  var 2
```

```lean
-- xy + z̄ 를 BoolExpr로 표현
def expr_xy_plus_nz : BoolExpr :=
  BoolExpr.or
    (BoolExpr.and (BoolExpr.var 0) (BoolExpr.var 1))
    (BoolExpr.not (BoolExpr.var 2))
```

### 4.2 부울 식의 평가 (값 계산)

부울 식에 변수값을 대입하여 결과를 계산하는 함수:

```lean
-- 환경(environment): 각 변수에 Bool 값을 대응시키는 함수
def BoolExpr.eval (env : Nat → Bool) : BoolExpr → Bool
  | .lit b => b
  | .var n => env n
  | .not e => !(e.eval env)
  | .and e₁ e₂ => (e₁.eval env) && (e₂.eval env)
  | .or e₁ e₂ => (e₁.eval env) || (e₂.eval env)
```

---

## 5. 부울 함수의 동치 — "겉모습은 달라도 기능은 같다"

두 부울 식이 **동치**(equivalent)라 함은, 모든 가능한 입력에 대해 같은 출력을 내는 것이다.

> 🎭 **비유**: 두 요리 레시피가 완전히 다르게 생겼지만, 똑같은 요리가 나온다면 두 레시피는 "동치"이다.

**예**: $xy$, $xy + 0$, $xy \cdot 1$은 모두 동치이다. 어떤 $x, y$ 값을 넣어도 결과가 같다.

```lean
-- 동치를 Lean 4로 표현
def boolFuncEquiv (f g : Bool → Bool → Bool) : Prop :=
  ∀ x y, f x y = g x y

-- xy와 xy + 0은 동치임을 증명
example : boolFuncEquiv
  (fun x y => x && y)
  (fun x y => (x && y) || false) := by
  intro x y
  simp [Bool.or_false]

-- xy와 xy · 1은 동치임을 증명
example : boolFuncEquiv
  (fun x y => x && y)
  (fun x y => (x && y) && true) := by
  intro x y
  simp [Bool.and_true]
```

---

## 6. Lean 4의 `Bool` 타입 — 기본 부울 연산 완전 정복

Lean 4에서 `Bool`은 정확히 두 값 `true`와 `false`를 가지는 타입이다:

```lean
#check Bool        -- Type
#check true        -- Bool
#check false       -- Bool
```

### 6.1 `Bool`의 기본 연산들

| 연산 | Lean 4 기호 | 함수 이름 |
|------|-----------|---------|
| NOT (보수) | `!x` | `Bool.not` |
| AND (곱) | `x && y` | `Bool.and` |
| OR (합) | `x \|\| y` | `Bool.or` |
| XOR (배타적 합) | `x ^^ y` | `Bool.xor` |

### 6.2 `decide` — 부울 명제의 자동 증명

Lean 4에서 `Bool`에 관한 간단한 명제는 `decide` 전략으로 자동 증명할 수 있다. `decide`는 유한한 경우를 모두 확인하여 증명한다:

```lean
-- decide로 간단한 부울 항등식 증명
example : ∀ x : Bool, !(!x) = x := by decide
example : ∀ x : Bool, x && true = x := by decide
example : ∀ x : Bool, x || false = x := by decide
example : ∀ x y : Bool, x && y = y && x := by decide
example : ∀ x y : Bool, x || y = y || x := by decide
```

> 💡 `decide`는 "결정 가능"(decidable)한 명제에 대해 모든 경우를 기계적으로 확인하는 전략이다. `Bool`은 값이 `true`와 `false` 두 개뿐이므로, 변수가 몇 개든 유한한 조합만 확인하면 된다.

---

## 7. 연습문제: 괄호 채우기 (Skeleton)

### 연습 7.1: 부울 식 값 계산

다음 부울 식의 값을 구하고, Lean 4로 확인하라.

```lean
-- (a) 1 · 0 의 값
-- 힌트: AND 연산이다
example : (true && false) = ⟨YOUR_ANSWER⟩ := by decide

-- (b) 1 + 1 의 값
-- 힌트: OR 연산이다. 1 + 1 = ?  (부울 합!)
example : (true || true) = ⟨YOUR_ANSWER⟩ := by decide

-- (c) 0̄ 의 값
-- 힌트: 0의 보수는?
example : (!false) = ⟨YOUR_ANSWER⟩ := by decide

-- (d) 1 · 1 + 0̄ 의 값
-- 힌트: 우선순위에 주의! 보수 → 곱 → 합
example : ((true && true) || (!false)) = ⟨YOUR_ANSWER⟩ := by decide
```

<details>
<summary>📝 답 보기</summary>

```lean
example : (true && false) = false := by decide
example : (true || true) = true := by decide
example : (!false) = true := by decide
example : ((true && true) || (!false)) = true := by decide
```

풀이:
- (a) $1 \cdot 0 = 0$ (AND: 둘 다 1이어야 1)
- (b) $1 + 1 = 1$ (OR: 하나라도 1이면 1)
- (c) $\overline{0} = 1$ (보수: 뒤집기)
- (d) $1 \cdot 1 + \overline{0} = 1 + 1 = 1$

</details>

### 연습 7.2: 부울 함수 정의하기

다음 부울 함수를 Lean 4로 정의하고, 모든 입력에 대한 값을 확인하라.

```lean
-- F(x, y, z) = x + yz 를 정의하라
def F_7_2 (x y z : Bool) : Bool := ⟨YOUR_EXPRESSION⟩

-- 확인: F(1, 1, 0) = ?
#eval F_7_2 true true false   -- 예상 결과: ⟨?⟩
-- 확인: F(0, 1, 1) = ?
#eval F_7_2 false true true   -- 예상 결과: ⟨?⟩
```

<details>
<summary>📝 답 보기</summary>

```lean
def F_7_2 (x y z : Bool) : Bool := x || (y && z)

#eval F_7_2 true true false   -- true  (1 + 1·0 = 1 + 0 = 1)
#eval F_7_2 false true true   -- true  (0 + 1·1 = 0 + 1 = 1)
#eval F_7_2 false false true  -- false (0 + 0·1 = 0 + 0 = 0)
#eval F_7_2 false false false -- false (0 + 0·0 = 0 + 0 = 0)
```

</details>

### 연습 7.3: `decide`로 증명하기

다음 부울 항등식을 `decide`로 증명하라.

```lean
-- (a) 이중 보수 법칙: not (not x) = x
example : ∀ x : Bool, !(!x) = ⟨YOUR_ANSWER⟩ := by ⟨YOUR_TACTIC⟩

-- (b) 교환 법칙: x && y = y && x
example : ∀ x y : Bool, x && y = ⟨YOUR_ANSWER⟩ := by ⟨YOUR_TACTIC⟩

-- (c) 항등 법칙: x || false = x
example : ∀ x : Bool, x || false = ⟨YOUR_ANSWER⟩ := by ⟨YOUR_TACTIC⟩

-- (d) 지배 법칙: x && false = false
example : ∀ x : Bool, x && false = ⟨YOUR_ANSWER⟩ := by ⟨YOUR_TACTIC⟩
```

<details>
<summary>📝 답 보기</summary>

```lean
example : ∀ x : Bool, !(!x) = x := by decide
example : ∀ x y : Bool, x && y = y && x := by decide
example : ∀ x : Bool, x || false = x := by decide
example : ∀ x : Bool, x && false = false := by decide
```

</details>

### 연습 7.4: 부울 함수의 동치 증명

```lean
-- xy + 0 = xy 임을 증명하라
-- 힌트: 모든 x, y에 대해 성립함을 보여야 한다
example : ∀ x y : Bool, (x && y) || false = ⟨YOUR_EXPRESSION⟩ := by
  ⟨YOUR_TACTIC⟩
```

<details>
<summary>📝 답 보기</summary>

```lean
example : ∀ x y : Bool, (x && y) || false = x && y := by decide
```

</details>

---

## 8. 연습문제: `sorry`로 직접 증명하기 (도전)

이제 `decide`를 사용하지 않고, 직접 경우 분석(case split)으로 증명해 보자.

### 연습 8.1: 경우 분석으로 이중 보수 증명

```lean
-- decide 없이 이중 보수 법칙을 증명하라
-- 힌트: Bool은 true와 false 두 경우뿐이므로, cases로 나누면 된다
example : ∀ x : Bool, !(!x) = x := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
example : ∀ x : Bool, !(!x) = x := by
  intro x
  cases x
  · -- x = false 인 경우: !(!false) = !(true) = false ✓
    rfl
  · -- x = true 인 경우: !(!true) = !(false) = true ✓
    rfl
```

**해설**: `cases x`는 `x : Bool`을 `true`와 `false` 두 경우로 나눈다. 각 경우에서 계산하면 양변이 같으므로 `rfl`(반사성)로 증명된다.

</details>

### 연습 8.2: 경우 분석으로 드 모르간 법칙 증명

```lean
-- 드 모르간 법칙: !(x && y) = (!x) || (!y)
example : ∀ x y : Bool, !(x && y) = (!x) || (!y) := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
example : ∀ x y : Bool, !(x && y) = (!x) || (!y) := by
  intro x y
  cases x <;> cases y <;> rfl
```

**해설**: `cases x <;> cases y`는 $x$와 $y$ 각각을 `true`/`false`로 나누어 총 4가지 경우를 만든다. `<;>`는 "모든 남은 목표에 다음 전략을 적용하라"는 뜻이다. 4가지 경우 모두 계산하면 양변이 같으므로 `rfl`로 끝난다.

| $x$ | $y$ | $\lnot(x \land y)$ | $\lnot x \lor \lnot y$ | 같은가? |
|-----|-----|--------------------|------------------------|--------|
| T   | T   | $\lnot T = F$      | $F \lor F = F$          | ✓ |
| T   | F   | $\lnot F = T$      | $F \lor T = T$          | ✓ |
| F   | T   | $\lnot F = T$      | $T \lor F = T$          | ✓ |
| F   | F   | $\lnot F = T$      | $T \lor T = T$          | ✓ |

</details>

### 연습 8.3: 분배 법칙 증명

```lean
-- 분배 법칙: x && (y || z) = (x && y) || (x && z)
-- Rosen 예제 8에 해당
example : ∀ x y z : Bool, x && (y || z) = (x && y) || (x && z) := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
example : ∀ x y z : Bool, x && (y || z) = (x && y) || (x && z) := by
  intro x y z
  cases x <;> cases y <;> cases z <;> rfl
```

**해설**: 3개의 변수를 각각 2가지 경우로 나누면 $2^3 = 8$가지 경우가 된다. 모든 경우에서 양변이 계산적으로 같으므로 `rfl`로 증명된다. 이것이 바로 **진리표를 이용한 증명**을 Lean 4로 형식화한 것이다!

</details>

### 연습 8.4: 흡수 법칙 증명

```lean
-- 흡수 법칙: x && (x || y) = x
-- Rosen 예제 10에 해당
example : ∀ x y : Bool, x && (x || y) = x := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
example : ∀ x y : Bool, x && (x || y) = x := by
  intro x y
  cases x <;> cases y <;> rfl

-- 또는 simp를 사용할 수도 있다
example : ∀ x y : Bool, x && (x || y) = x := by
  intro x y
  simp [Bool.and_or_self]
```

</details>

---

## 9. `Prop` 세계에서의 부울 법칙들 — 격자와 BooleanAlgebra

지금까지 `Bool` 타입에서 `decide`나 `cases`로 부울 법칙을 증명했다. 이제 한 단계 올라가서, Lean 4의 **타입클래스 계층**을 통해 부울 대수를 추상적으로 다루는 방법을 소개한다.

### 9.1 격자(Lattice)에서의 부울 법칙

『Mathematics in Lean』에서 다루는 **격자**(Lattice)는 부울 대수의 일반화이다:

| 부울 대수 | 격자 | Lean 4 기호 |
|----------|------|-----------|
| $x \cdot y$ (AND) | **하한**(infimum, meet) | `x ⊓ y` |
| $x + y$ (OR) | **상한**(supremum, join) | `x ⊔ y` |
| 0 | **최소 원소**(bottom) | `⊥` |
| 1 | **최대 원소**(top) | `⊤` |
| $\overline{x}$ (보수) | **여원소**(complement) | `xᶜ` |

```lean
-- 격자의 기본 공리들
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check (inf_le_left : x ⊓ y ≤ x)       -- x ⊓ y ≤ x
#check (inf_le_right : x ⊓ y ≤ y)      -- x ⊓ y ≤ y
#check (le_sup_left : x ≤ x ⊔ y)       -- x ≤ x ⊔ y
#check (le_sup_right : y ≤ x ⊔ y)      -- y ≤ x ⊔ y
```

### 9.2 분배 격자와 부울 대수

**분배 격자**(DistribLattice)는 분배 법칙이 성립하는 격자이다:

```lean
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

-- 분배 법칙
#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
```

**부울 대수**(BooleanAlgebra)는 분배 격자에 **보수**(complement)를 추가한 것이다:

```lean
variable {α : Type*} [BooleanAlgebra α]
variable (x y : α)

-- 보수 법칙
#check (inf_compl_eq_bot : x ⊓ xᶜ = ⊥)    -- x AND (NOT x) = 0
#check (sup_compl_eq_top : x ⊔ xᶜ = ⊤)    -- x OR (NOT x) = 1

-- 드 모르간 법칙
#check (compl_inf : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ)
#check (compl_sup : (x ⊔ y)ᶜ = xᶜ ⊓ yᶜ)
```

> 💡 **핵심**: `BooleanAlgebra`는 Rosen의 **정의 1**(12.1.5절)에 해당한다. 항등 법칙, 보수 법칙, 결합 법칙, 교환 법칙, 분배 법칙을 모두 만족하는 추상적 구조이다.

---

## 10. 핵심 요약

| 개념 | 의미 | Lean 4 |
|------|------|--------|
| **부울 보수**(complement) | 0↔1 뒤집기 | `!x`, `xᶜ` |
| **부울 합**(OR) | 하나라도 1이면 1 | `x \|\| y`, `x ⊔ y` |
| **부울 곱**(AND) | 둘 다 1이어야 1 | `x && y`, `x ⊓ y` |
| **부울 변수** | 0 또는 1만 가능 | `x : Bool` |
| **부울 함수** | $B^n \to B$ | `Bool → ... → Bool` |
| **$n$차 부울 함수 수** | $2^{2^n}$ | `2 ^ (2 ^ n)` |
| **동치** | 모든 입력에서 같은 출력 | `∀ x y ..., f = g` |
| `decide` | 유한 경우 자동 확인 | `by decide` |
| `cases` + `rfl` | 경우 분석 후 계산 | `cases x <;> rfl` |
| `BooleanAlgebra` | 추상적 부울 대수 | `[BooleanAlgebra α]` |

---

## 다음 파트 예고

**Part 14-B**에서는:
- **부울 대수의 항등식들**(표 5의 모든 법칙)을 체계적으로 정리하고 Lean 4로 증명
- **쌍대성**(duality)의 원리
- **곱의 합 표준형**(sum-of-products expansion / disjunctive normal form)
- **함수적 완전성**(functional completeness): NAND와 NOR 하나로 모든 것을 표현
- 12.2절의 핵심 내용을 다룬다.
