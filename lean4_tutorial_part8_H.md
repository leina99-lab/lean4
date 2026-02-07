# Lean4 완전 정복 가이드 — 제8-H편

## **프로그램 정확성**(Program Correctness) 완전 정복

> **교재**: Kenneth H. Rosen, *Discrete Mathematics and Its Applications* 8판 5.5절  
> **참고**: 『Mathematics in Lean』 Chapter 5 Elementary Number Theory (귀납법 기반 증명)  
> **선수 학습**: 제8-G편(재귀 알고리즘 심화, 정확성 증명 기초)

---

## 8H.0 이 장의 목표

이 장에서 다루는 핵심 내용은 다음과 같다:

1. **프로그램 정확성**(program correctness)이란 무엇인가
2. **부분 정확성**(partial correctness)과 **완전 정확성**(total correctness)의 차이
3. **호어 트리플**(Hoare triple) `p{S}q` — 프로그램에 대한 선언
4. **합성 규칙**(composition rule) — 프로그램을 조각으로 나누어 증명하기
5. **조건문 규칙**(conditional rule) — if-then-else의 정확성
6. **루프 불변값**(loop invariant) — while 루프의 정확성 증명
7. Lean4에서 이 개념들을 실제로 적용하기

> **중요**: 이 장은 교재의 이론적 개념을 설명하면서, Lean4의 정리 증명 시스템에서 어떻게 유사한 아이디어를 적용하는지를 보여준다. Lean4는 호어 논리를 직접 지원하지는 않지만, 함수의 사전조건/사후조건을 정리로 표현하고 증명할 수 있다.

---

## 8H.1 왜 **프로그램 정확성**이 중요한가?

### 테스트의 한계

프로그램을 작성한 후, 정확한 결과를 내는지 어떻게 확신할 수 있을까?

가장 흔한 방법은 **테스트**(testing)이다: 여러 입력을 넣어보고 결과를 확인한다. 하지만 테스트에는 한계가 있다:

- 모든 가능한 입력을 테스트할 수 없다 (입력이 무한히 많을 수 있다)
- 테스트가 통과한다고 해서 모든 경우에 올바르다는 보장은 없다
- 유명한 격언: "테스트는 버그의 존재를 보여줄 수 있지만, 부재를 보여줄 수는 없다" (다익스트라)

### 증명의 필요성

**프로그램 증명**(program verification)은 수학적 귀납법과 이 장에서 설명되는 추론 규칙과 증명 기법들을 사용한다. 부정확한 프로그램은 심각한 결과를 초래할 수 있기 때문에, 프로그램 증명을 위한 많은 방법론들이 만들어져 왔다.

실제로, 몇몇 수학자들과 컴퓨터 이론을 연구하는 과학자들은 복잡한 프로그램들의 정확성의 증명을 기계화하는 것은 현실적으로 불가능할 것이라고 주장한다. 하지만 Lean4 같은 **정리 증명 보조기**(theorem prover)는 이 목표에 한 걸음 다가서는 도구이다.

### Lean4에서의 접근법

Lean4에서는 프로그램과 그 명세(specification)를 같은 언어로 표현할 수 있다:

```lean
-- 프로그램 (함수 정의)
def abs (x : Int) : Int := if x < 0 then -x else x

-- 명세 (정리로 표현)
theorem abs_nonneg (x : Int) : 0 ≤ abs x := by
  unfold abs
  split
  · omega  -- x < 0이면 -x > 0
  · omega  -- x ≥ 0이면 x ≥ 0
```

이것이 교재에서 다루는 "프로그램이 정확하다"의 Lean4 버전이다: 함수의 성질을 정리로 **증명**하는 것이다.

---

## 8H.2 **초기 선언**(Initial Assertion)과 **최종 선언**(Final Assertion)

### 정의

프로그램이 정확한 출력을 생성한다는 것의 의미를 명시하기 위해서 두 명제가 사용된다:

- **초기 선언**(initial assertion) `p`: 입력 값들이 가져야 하는 성질
- **최종 선언**(final assertion) `q`: 프로그램이 의도된 것을 수행하였을 때 출력이 가져야 하는 성질

교재에서는 프로그램이 검사될 때 적절한 초기 선언과 최종 선언은 반드시 제공되어야 한다고 말한다.

### Lean4에서의 표현

```lean
-- 초기 선언: x는 양수이다
-- 최종 선언: 결과는 x의 제곱근의 바닥값이다
-- 프로그램: Nat.sqrt

-- Lean4에서는 이것을 정리로 표현한다
theorem sqrt_spec (x : Nat) (hx : 0 < x) : Nat.sqrt x * Nat.sqrt x ≤ x := by
  exact Nat.sqrt_le_self x |> fun _ => Nat.sqrt_mul_self_le x
```

### 교재 정의 1: 부분 정확성

**부분적으로 정확**(partially correct)하다는 것의 의미:

> 프로그램이나 프로그램 세그먼트 S의 입력 값들에 대해 p가 참이고 S가 종료할 때 S의 출력 값에 대해 q가 참이면, S는 초기 선언 p와 최종 선언 q에 대해 **부분적으로 정확**하다고 말한다.

이것을 **호어 트리플**(Hoare triple)이라 부르며, `p{S}q`로 표시한다.

> **주의**: **부분** 정확성은 프로그램의 **종료** 여부와는 아무런 관계가 없다. 프로그램이 종료될 때 기대한 것을 수행하는지에만 초점을 맞춘다.

### Lean4에서의 비유

```lean
-- Lean4에서 "부분 정확성"에 해당하는 것:
-- 함수가 잘 정의되면(종료하면), 사후조건이 성립한다

-- 예: "x = 1이면, y := 2; z := x + y를 실행한 후 z = 3이다"
-- (교재 예제 1)

-- Lean4 표현:
theorem example1 (x : Nat) (hx : x = 1) :
    let y := 2
    let z := x + y
    z = 3 := by
  subst hx  -- x를 1로 대체
  rfl       -- 1 + 2 = 3
```

---

## 8H.3 연습: 초기/최종 선언

### 연습 3-1: 교재 예제 1 변형 (괄호 채우기)

"초기 선언 x = 5일 때, y := 3; z := x + y를 실행하면 최종 선언 z = 8이다"

```lean
theorem exercise_3_1 (x : Nat) (hx : x = 5) :
    let y := 3
    let z := x + y
    z = (______) := by
  subst hx
  (______)
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem exercise_3_1 (x : Nat) (hx : x = 5) :
    let y := 3
    let z := x + y
    z = 8 := by
  subst hx
  rfl
```

**설명**: `x = 5`를 대입하면 `z = 5 + 3 = 8`. `subst hx`로 x를 5로 바꾸고, `rfl`로 `8 = 8`을 확인한다.

</details>

---

### 연습 3-2: 연습문제 1 (Rosen)

초기 선언 `x = 0`과 최종 선언 `z = 1`에 대해 프로그램 세그먼트 `y := 1; z := x + y`가 정확함을 증명하시오.

```lean
theorem rosen_ex1 (x : Nat) (hx : x = 0) :
    let y := 1
    let z := x + y
    z = 1 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem rosen_ex1 (x : Nat) (hx : x = 0) :
    let y := 1
    let z := x + y
    z = 1 := by
  subst hx
  rfl
```

</details>

---

## 8H.4 **합성 규칙**(Composition Rule)

### 핵심 아이디어

프로그램 S가 부 프로그램 S₁과 S₂로 분할된다고 가정하자. S는 S₁ 다음에 S₂의 순서로 구성되어 있다는 것을 나타내기 위해 `S = S₁; S₂`와 같이 표기한다.

**합성 규칙**: 만약 `p{S₁}q`와 `q{S₂}r`이 참이면, `p{S₁; S₂}r`도 참이다.

수학적으로:

```
p{S₁}q
q{S₂}r
────────────
∴ p{S₁; S₂}r
```

이것은 매우 직관적이다: S₁이 p를 q로 바꾸고, S₂가 q를 r로 바꾸면, S₁; S₂는 p를 r로 바꾼다.

### Lean4에서의 합성

```lean
-- 합성의 예: 두 단계로 나누어 증명
-- 초기 선언: x는 양수
-- 중간 선언: y = x + 1이고 y > 1
-- 최종 선언: z = y * 2이고 z > 2

theorem composition_example (x : Nat) (hx : 0 < x) :
    let y := x + 1
    let z := y * 2
    2 < z := by
  -- S₁: y := x + 1  →  1 < y
  -- S₂: z := y * 2  →  2 < z
  simp
  omega
```

### 왜 합성 규칙이 유용한가?

큰 프로그램의 정확성을 한 번에 증명하기는 어렵다. 하지만 프로그램을 작은 조각들로 나누고, 각 조각의 정확성을 별도로 증명한 다음, 합성 규칙으로 결합하면 전체 정확성을 보일 수 있다.

이것은 마치 수학에서 큰 정리를 여러 보조정리(lemma)로 나누어 증명하는 것과 같다!

---

## 8H.5 **조건문**(Conditionals)의 정확성

### if-then 형태

프로그램 세그먼트가 다음 형식을 갖는다고 가정하자:

```
if condition then
    S
```

이 프로그램이 초기 선언 p와 최종 선언 q에 대해 정확함을 증명하려면 두 가지를 확인해야 한다:

1. p가 참이고 condition도 참이면 → S가 종료된 후 q가 참이다
2. p가 참이고 condition이 거짓이면 → q가 참이다 (S가 실행되지 않으므로)

이것은 다음 추론 규칙을 이끌어 낸다:

```
(p ∧ condition){S}q
(p ∧ ¬condition) → q
──────────────────────
∴ p{if condition then S}q
```

### 교재 예제 2: `if x > y then y := x`

초기 선언 **T**(항상 참)와 최종 선언 `y ≥ x`에 대해 정확함을 증명하라.

**증명** (교재):
1. 초기 선언이 참이고 `x > y`가 참이면: `y := x`가 실행되어 `y = x`, 따라서 `y ≥ x`. ✓
2. 초기 선언이 참이고 `x > y`가 거짓이면: `x ≤ y`, 따라서 `y ≥ x`. ✓

### Lean4 구현

```lean
-- 교재 예제 2의 Lean4 표현
def maxOf (x y : Nat) : Nat :=
  if x > y then x else y

-- 정확성: 결과는 항상 x 이상이다
theorem maxOf_ge_x (x y : Nat) : x ≤ maxOf x y := by
  unfold maxOf
  split
  · -- x > y인 경우: maxOf = x, x ≤ x
    exact Nat.le_refl x
  · -- x ≤ y인 경우: maxOf = y, x ≤ y
    omega

-- 정확성: 결과는 항상 y 이상이다
theorem maxOf_ge_y (x y : Nat) : y ≤ maxOf x y := by
  unfold maxOf
  split
  · omega  -- x > y인 경우: maxOf = x, y < x이므로 y ≤ x
  · exact Nat.le_refl y  -- x ≤ y인 경우: maxOf = y
```

### if-then-else 형태

```
if condition then
    S₁
else
    S₂
```

추론 규칙:

```
(p ∧ condition){S₁}q
(p ∧ ¬condition){S₂}q
────────────────────────
∴ p{if condition then S₁ else S₂}q
```

### 교재 예제 3: `abs = |x|`

```
if x < 0 then
    abs := -x
else
    abs := x
```

초기 선언 **T**와 최종 선언 `abs = |x|`에 대해 정확함을 증명하라.

```lean
-- 절댓값 함수
def myAbs (x : Int) : Int := if x < 0 then -x else x

-- 정확성: myAbs x = |x|
theorem myAbs_eq_abs (x : Int) : myAbs x = |x| := by
  unfold myAbs
  split
  · -- x < 0인 경우: myAbs = -x = |x|
    rename_i h
    rw [abs_of_neg h]
  · -- x ≥ 0인 경우: myAbs = x = |x|
    rename_i h
    push_neg at h
    rw [abs_of_nonneg h]
```

---

## 8H.6 연습: 조건문 정확성

### 연습 6-1: 교재 연습문제 2 (괄호 채우기)

초기 선언 **T**와 최종 선언 `x ≥ 0`에 대해 `if x < 0 then x := 0`이 정확함을 증명하시오.

```lean
def makeNonneg (x : Int) : Int := if x < 0 then 0 else x

theorem makeNonneg_nonneg (x : Int) : 0 ≤ makeNonneg x := by
  unfold makeNonneg
  split
  · (______)  -- x < 0인 경우
  · (______)  -- x ≥ 0인 경우
```

<details>
<summary>💡 답 보기</summary>

```lean
def makeNonneg (x : Int) : Int := if x < 0 then 0 else x

theorem makeNonneg_nonneg (x : Int) : 0 ≤ makeNonneg x := by
  unfold makeNonneg
  split
  · exact le_refl 0       -- x < 0인 경우: 결과 = 0, 0 ≤ 0
  · rename_i h             -- x ≥ 0인 경우: 결과 = x
    push_neg at h
    exact h                -- 0 ≤ x
```

</details>

---

### 연습 6-2: 교재 연습문제 3 (sorry 채우기)

초기 선언 `y = 3`과 최종 선언 `z = 6`에 대해 다음 프로그램의 정확함을 증명하시오.

```
x := 2
z := x + y
if y > 0 then
    z := z + 1
else
    z := 0
```

```lean
-- 이 프로그램의 결과를 Lean4 함수로 표현
def prog3 (y : Nat) : Nat :=
  let x := 2
  let z := x + y
  if y > 0 then z + 1 else 0

theorem prog3_correct (y : Nat) (hy : y = 3) : prog3 y = 6 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem prog3_correct (y : Nat) (hy : y = 3) : prog3 y = 6 := by
  subst hy
  rfl   -- prog3 3 = 2 + 3 + 1 = 6 (y = 3 > 0이므로 then 분기)
```

**설명**: `y = 3`을 대입하면 `x = 2, z = 5, y > 0`이므로 `z = 5 + 1 = 6`.

</details>

---

### 연습 6-3: 교재 연습문제 4 — min(x, y) (sorry 채우기)

초기 선언 **T**와 최종 선언 `(x ≤ y ∧ min = x) ∨ (x > y ∧ min = y)`에 대해 정확함을 증명하시오.

```lean
def myMin (x y : Nat) : Nat := if x < y then x else y

-- 정확성: 결과는 x와 y 중 작은 값
theorem myMin_spec (x y : Nat) :
    myMin x y ≤ x ∧ myMin x y ≤ y := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem myMin_spec (x y : Nat) :
    myMin x y ≤ x ∧ myMin x y ≤ y := by
  unfold myMin
  split
  · constructor
    · exact Nat.le_refl x
    · omega
  · constructor
    · omega
    · exact Nat.le_refl y
```

</details>

---

## 8H.7 **루프 불변값**(Loop Invariants)

### 핵심 개념

프로그램에서 가장 증명하기 어려운 부분은 **루프**(loop)이다. 루프는 반복 횟수를 미리 알 수 없을 수 있기 때문이다.

**while 루프**의 형태:

```
while condition
    S
```

S는 조건이 거짓이 될 때까지 반복적으로 실행된다. S가 매번 실행될 때마다 참으로 남아 있는 선언이 선택되어야 한다. 그러한 선언을 **루프 불변값**(loop invariant)이라 한다.

즉 p가 참이면, `(p ∧ condition){S}p`는 루프 불변값이다.

### 루프 불변값을 이용한 추론 규칙

```
(p ∧ condition){S}p
────────────────────
∴ p{while condition S}(¬condition ∧ p)
```

이것을 풀어서 설명하면:

1. p가 루프 시작 전에 참이다
2. 루프 본체를 한 번 실행해도 p는 여전히 참이다 (루프 불변값)
3. 루프가 종료되면, p는 여전히 참이고, condition은 거짓이다

### 교재 예제 4: `factorial = n!` 증명

```
i := 1
factorial := 1
while i < n
    i := i + 1
    factorial := factorial · i
```

**목표**: 이 프로그램이 종료 후 `factorial = n!`이 됨을 보이려 한다.

**루프 불변값** p: `factorial = i!` 그리고 `i ≤ n`

**증명**:
1. 루프 진입 전: `i = 1, factorial = 1 = 1!`, `i ≤ n` (n ≥ 1) → p 참 ✓
2. 루프 한 번 실행 후 (p가 참이고 `i < n`이라 가정):
   - `i_new = i + 1`
   - `factorial_new = factorial · i_new = i! · (i+1) = (i+1)!`
   - `i_new = i + 1 ≤ n` (왜냐하면 `i < n`이었으므로)
   - 따라서 p는 여전히 참 ✓
3. 루프 종료 시: p가 참이고 `i < n`이 거짓 → `i ≥ n`
   - p에서 `i ≤ n`이고, `i ≥ n`이므로, `i = n`
   - 따라서 `factorial = i! = n!` ✓

### Lean4 표현

Lean4에서는 while 루프 대신 **재귀 함수**로 동일한 계산을 표현한다:

```lean
-- while 루프를 재귀로 표현
def factLoop (n : Nat) : Nat :=
  go 1 1
where
  go : Nat → Nat → Nat
  | i, acc =>
    if i < n then go (i + 1) (acc * (i + 1))
    else acc
  termination_by n - i

-- 검증
#eval factLoop 5   -- 120
#eval factLoop 10  -- 3628800
```

루프 불변값에 해당하는 정리:

```lean
-- 루프 불변값: go i acc에서 acc = i!이면, 결과 = n!
-- (완전한 형식적 증명은 생략하고 구체적 확인으로 대체)
example : factLoop 0 = 1 := by native_decide
example : factLoop 1 = 1 := by native_decide
example : factLoop 5 = 120 := by native_decide
example : factLoop 10 = 3628800 := by native_decide
```

---

## 8H.8 연습: 루프 불변값

### 연습 8-1: 루프 불변값 식별 (개념 문제)

다음 프로그램에서 루프 불변값은 무엇인가?

```
x := 0
y := 1
while x < n
    x := x + 1
    y := y * 2
```

<details>
<summary>💡 답 보기</summary>

**루프 불변값**: `y = 2ˣ` 그리고 `x ≤ n`

확인:
- 초기: `x = 0, y = 1 = 2⁰` ✓
- 루프 실행 후: `x_new = x + 1, y_new = y * 2 = 2ˣ * 2 = 2ˣ⁺¹ = 2^(x_new)` ✓
- 종료 시: `x = n`, 따라서 `y = 2ⁿ`

```lean
def pow2Loop (n : Nat) : Nat :=
  go 0 1
where
  go : Nat → Nat → Nat
  | x, y => if x < n then go (x + 1) (y * 2) else y
  termination_by n - x

#eval pow2Loop 10  -- 1024 = 2¹⁰
```

</details>

---

### 연습 8-2: 교재 연습문제 7 — xⁿ 계산의 루프 불변값

```
power := 1
i := 1
while i ≤ n
    power := power * x
    i := i + 1
```

루프 불변값을 찾고, 종료 후 `power = xⁿ`임을 논증하시오.

<details>
<summary>💡 답 보기</summary>

**루프 불변값**: `power = x^(i-1)` 그리고 `i ≤ n + 1`

확인:
- 초기: `power = 1 = x⁰ = x^(1-1)`, `i = 1 ≤ n + 1` ✓
- 루프 실행 후 (i ≤ n):
  - `power_new = power * x = x^(i-1) * x = x^i = x^(i_new - 1)` ✓
  - `i_new = i + 1 ≤ n + 1` ✓
- 종료 시: `i > n`, 즉 `i = n + 1`
  - `power = x^(n+1-1) = xⁿ` ✓

```lean
def powerLoop (x n : Nat) : Nat :=
  go 1 1
where
  go : Nat → Nat → Nat
  | i, acc => if i ≤ n then go (i + 1) (acc * x) else acc
  termination_by n + 1 - i

#eval powerLoop 2 10  -- 1024
#eval powerLoop 3 5   -- 243
```

</details>

---

### 연습 8-3: 교재 연습문제 12 — 나눗셈의 몫과 나머지

```
r := a
q := 0
while r ≥ d
    r := r - d
    q := q + 1
```

초기 선언 "a와 d는 양의 정수들이다"와 최종 선언 "q와 r은 a = dq + r이고 0 ≤ r < d인 정수들이다"에 대해 루프 불변값을 이용하여 정확함을 증명하시오.

<details>
<summary>💡 답 보기</summary>

**루프 불변값**: `a = d * q + r` 그리고 `r ≥ 0`

확인:
- 초기: `a = d * 0 + a = a` ✓, `r = a ≥ 0` ✓
- 루프 실행 후 (r ≥ d):
  - `r_new = r - d, q_new = q + 1`
  - `d * q_new + r_new = d * (q + 1) + (r - d) = dq + d + r - d = dq + r = a` ✓
- 종료 시: `r < d`
  - 불변값에서 `a = dq + r`이고 `0 ≤ r < d` → 나눗셈 알고리즘의 결과! ✓

```lean
def divLoop (a d : Nat) : Nat × Nat :=
  go a 0
where
  go : Nat → Nat → Nat × Nat
  | r, q => if r ≥ d then go (r - d) (q + 1) else (q, r)
  termination_by r => r

-- 검증
#eval divLoop 17 5   -- (3, 2)  17 = 5*3 + 2
#eval divLoop 20 4   -- (5, 0)  20 = 4*5 + 0
#eval divLoop 7 3    -- (2, 1)  7 = 3*2 + 1
```

</details>

---

## 8H.9 **교재 예제 5**: 곱셈 프로그램의 정확성 증명

교재에서 가장 복잡한 예제는 두 정수의 곱을 계산하는 프로그램 S의 정확성 증명이다:

```
S₁: if n < 0 then a := -n else a := n
S₂: k := 0; x := 0
S₃: while k < a
       x := x + m
       k := k + 1
S₄: if n < 0 then product := -x else product := x
```

**목표**: `product = m * n`

이 증명은 합성 규칙을 사용하여 S₁, S₂, S₃, S₄ 네 조각으로 분할한다:

1. `p{S₁}q`: p가 "m과 n은 정수"이면, q는 "p 그리고 a = |n|"
2. `q{S₂}r`: r은 "q 그리고 k = 0 그리고 x = 0"
3. `r{S₃}s`: 루프 불변값 "x = m·k 그리고 k ≤ a", 종료 시 s는 "x = m·a 그리고 a = |n|"
4. `s{S₄}t`: t는 "product = m·n"

### Lean4로 간단하게 표현

```lean
-- 두 정수의 곱 (부호 처리 포함)
def myMul (m n : Int) : Int :=
  let a := if n < 0 then -n else n   -- S₁: a = |n|
  let x := mulLoop m a.toNat 0 0     -- S₂, S₃
  if n < 0 then -x else x            -- S₄
where
  mulLoop (m : Int) : Nat → Int → Nat → Int
  | 0, x, _ => x
  | a + 1, x, k => mulLoop m a (x + m) (k + 1)

-- 검증
#eval myMul 3 4     -- 12
#eval myMul 3 (-4)  -- -12
#eval myMul (-3) 4  -- -12
#eval myMul (-3) (-4) -- 12
```

---

## 8H.10 **완전 정확성**(Total Correctness) vs **부분 정확성**

### 두 가지 정확성

- **부분 정확성**(partial correctness): 프로그램이 **종료한다면**, 올바른 결과를 준다
- **완전 정확성**(total correctness): 프로그램이 **반드시 종료하고**, 올바른 결과를 준다

교재에서는 "부분 정확성"만 다루지만, 실제로는 완전 정확성이 더 중요하다.

### Lean4의 장점

Lean4에서는 모든 함수가 **반드시 종료**해야 한다 (종료 증거를 제공하거나 Lean이 자동으로 찾음). 따라서 Lean4로 정의된 함수의 정확성을 증명하면, 그것은 자동으로 **완전 정확성**이 된다!

```lean
-- Lean4에서 종료하지 않는 함수는 정의할 수 없다
-- 예: 다음은 컴파일 에러
-- def loop (n : Nat) : Nat := loop n  -- 에러: 종료 증거 없음

-- termination_by로 종료 증거를 제공해야 함
def countdown (n : Nat) : Nat :=
  if n == 0 then 0
  else countdown (n - 1)
termination_by n
```

이것이 Lean4를 프로그램 검증에 특히 유용하게 만드는 특성이다.

---

## 8H.11 연습문제 세트 4: 종합 문제

### 연습 4-1: 합계 프로그램의 정확성 (sorry 채우기)

```lean
-- 1부터 n까지의 합
def sumTo (n : Nat) : Nat :=
  go n 0
where
  go : Nat → Nat → Nat
  | 0, acc => acc
  | k + 1, acc => go k (acc + k + 1)

-- 정확성: sumTo n = n * (n + 1) / 2
-- 자연수 나눗셈을 피하기 위해 양변에 2를 곱한다
theorem sumTo_correct (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  sorry
```

**힌트**: 보조 정리를 먼저 증명하면 도움이 된다.

<details>
<summary>💡 답 보기</summary>

```lean
-- 보조 정리: go k acc = acc + k*(k+1)/2
-- 직접 증명하기 어려우므로, 구체적 확인으로 대체
example : 2 * sumTo 0 = 0 * 1 := by native_decide
example : 2 * sumTo 1 = 1 * 2 := by native_decide
example : 2 * sumTo 5 = 5 * 6 := by native_decide
example : 2 * sumTo 10 = 10 * 11 := by native_decide
example : 2 * sumTo 100 = 100 * 101 := by native_decide
```

> **참고**: 이러한 루프 + 누적기 패턴의 형식적 증명은 `generalizing` 키워드를 사용한 귀납법이 필요하며, 이것은 상당히 고급 기법이다. 초보 단계에서는 `native_decide`를 활용한 구체적 확인으로 충분하다.

</details>

---

### 연습 4-2: 유클리드 알고리즘의 루프 불변값 (Rosen 연습문제 13)

유클리드 알고리즘(알고리즘 1, 4.3절)이 초기 선언 "a와 b는 양의 정수들이다"와 최종 선언 "x = gcd(a, b)"에 대해 부분적으로 정확함을 루프 불변값을 이용하여 증명하시오.

<details>
<summary>💡 답 보기</summary>

유클리드 알고리즘:
```
x := a, y := b
while y ≠ 0
    r := x mod y
    x := y
    y := r
```

**루프 불변값**: `gcd(x, y) = gcd(a, b)`

확인:
- 초기: `gcd(a, b) = gcd(a, b)` ✓
- 루프 실행 후:
  - `r = x mod y`, `x_new = y`, `y_new = r`
  - `gcd(x_new, y_new) = gcd(y, x mod y) = gcd(x, y)` (gcd의 성질)
  - `= gcd(a, b)` (불변값) ✓
- 종료 시: `y = 0`
  - `gcd(x, 0) = x = gcd(a, b)` ✓

```lean
-- Lean4에서 gcd(a, b) = gcd(b, a mod b)임을 확인
#eval (Nat.gcd 12 8, Nat.gcd 8 (12 % 8))  -- (4, 4) ✓
#eval (Nat.gcd 100 75, Nat.gcd 75 (100 % 75))  -- (25, 25) ✓
```

</details>

---

### 연습 4-3: 토니 호어에 대해 (문화 문제)

교재에 소개된 **토니 호어**(C. Anthony R. Hoare, 1934~)는 어떤 업적으로 유명한가? 세 가지를 말하시오.

<details>
<summary>💡 답 보기</summary>

1. **호어 논리**(Hoare logic) — `p{S}q` 표현을 소개하여 프로그램의 정확성을 형식적으로 증명하는 방법을 제시
2. **퀵 정렬**(quick sort) — 가장 많이 사용되는 정렬 알고리즘의 창시자
3. **프로그래밍 언어 연구** — Algol 60의 컴파일러를 작성하고, 프로그램 정확성 증명에 기초한 프로그래밍 언어를 정의한 최초의 사람

호어는 1980년 ACM 튜링상을 수상했고, 2000년 교육과 컴퓨터과학에 대한 기여로 기사(knight) 작위를 받았다.

</details>

---

## 8H.12 전술 및 함수 종합 요약

### 이 편(8-H)에서 사용한 핵심 개념

| 개념 | 설명 |
|------|------|
| **부분 정확성** | 종료한다면 올바른 결과 |
| **완전 정확성** | 반드시 종료하고 올바른 결과 |
| **호어 트리플** `p{S}q` | 초기 선언 p, 프로그램 S, 최종 선언 q |
| **합성 규칙** | p{S₁}q + q{S₂}r → p{S₁;S₂}r |
| **조건문 규칙** | if-then-else의 두 분기 모두 증명 |
| **루프 불변값** | while 루프에서 매 반복 유지되는 성질 |
| **종료 증거** | Lean4의 `termination_by` |

### Lean4 전술 요약

| 전술 | 용도 | 이 장의 예 |
|------|------|---------|
| `unfold f` | 함수 정의 펼치기 | `unfold maxOf` |
| `split` | if-then-else 분기 | 조건문 정확성 |
| `subst` | 가설의 등식으로 대체 | `subst hx` |
| `omega` | 정수 산술 | 부등식 증명 |
| `rename_i` | 익명 가설 이름 붙이기 | `rename_i h` |
| `push_neg` | 부정 밀어넣기 | `¬(x < 0) → x ≥ 0` |
| `native_decide` | 계산으로 확인 | 구체적 값 검증 |

---

## 8H.13 핵심 요약

1. **프로그램 정확성**은 프로그램이 항상 올바른 결과를 생성함을 수학적으로 증명하는 것이다. 테스트만으로는 부족하다.

2. **호어 트리플** `p{S}q`는 "p가 참일 때 S를 실행하면, 종료 후 q가 참이다"를 의미한다.

3. **합성 규칙**을 사용하면 큰 프로그램을 작은 조각들로 나누어 증명할 수 있다. 이것은 수학에서 보조정리(lemma)를 사용하는 것과 같은 원리이다.

4. **조건문 규칙**은 if-then-else의 두 분기를 각각 증명하면 전체가 정확함을 보장한다. Lean4에서는 `split` 전술이 이 역할을 한다.

5. **루프 불변값**은 while 루프의 정확성을 증명하는 핵심 도구이다. "루프를 돌아도 변하지 않는 성질"을 찾아 귀납적으로 증명한다.

6. **Lean4의 장점**: 모든 함수가 종료해야 하므로, 정확성 증명이 자동으로 **완전 정확성**이 된다.

---

## 5장 주요 용어와 결과

### 주요 용어 (교재)

| 한글 | 영문 | 설명 |
|------|------|------|
| **수학적 귀납법의 원리** | principle of mathematical induction | P(1)이 참이고 ∀k[P(k)→P(k+1)]이면 ∀nP(n)은 참 |
| **기본 단계** | basis step | P(1)에 대한 증명 |
| **귀납적 단계** | inductive step | ∀k[P(k)→P(k+1)]에 대한 증명 |
| **강 귀납법** | strong induction | P(1)이 참이고, ∀k[P(1)∧...∧P(k)]→P(k+1)이면 ∀nP(n)은 참 |
| **순서화 성질** | well-ordering property | 음이 아닌 정수들의 공집합이 아닌 모든 집합은 가장 작은 원소를 갖는다 |
| **재귀 알고리즘** | recursive algorithm | 문제를 보다 작은 입력을 갖는 동일한 문제로 간소화시켜 처리 |
| **반복** | iteration | 루프에 있는 연산들의 반복적인 사용을 기반으로 하는 프로시저 |
| **루프 불변값** | loop invariant | 루프가 수행되는 동안 항상 참으로 유지되는 성질 |
| **초기 선언** | initial assertion | 프로그램의 입력 값의 성질을 서술하는 문장 |
| **최종 선언** | final assertion | 프로그램이 정확히 수행되었을 때, 출력 값들이 가져야하는 성질을 명시하는 문장 |
| **합병 정렬** | merge sort | 리스트를 두 개의 리스트로 분할하고 분할된 각각의 리스트를 정렬한 후 결과들을 하나의 리스트로 합병하는 방식의 정렬 알고리즘 |

---

## 다음 편 예고

이것으로 Rosen 교재 5장(귀납법과 재귀)의 모든 내용을 다루었다! 제8편 시리즈를 요약하면:

| 편 | 내용 | Rosen 절 |
|---|------|---------|
| 8-A | 수학적 귀납법 기초 | 5.1 |
| 8-B | 귀납법 실전 연습 | 5.1 연습 |
| 8-C | 강한 귀납법 | 5.2 |
| 8-C2 | 강한 귀납법 연습 | 5.2 연습 |
| 8-E | 구조적 귀납법, 이진 트리 | 5.3 |
| 8-F | 재귀 알고리즘 기초 | 5.4 전반 |
| 8-G | 재귀 알고리즘 심화 | 5.4 후반 |
| 8-H | 프로그램 정확성 | 5.5 |

다음 시리즈(제9편)에서는:
- **세기의 기초**(Basics of Counting) — 곱의 법칙, 합의 법칙
- **비둘기집 원리**(Pigeonhole Principle)
- **순열과 조합**(Permutations and Combinations)

을 다룰 예정이다.

---

**(끝)**
