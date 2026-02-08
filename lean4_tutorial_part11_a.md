# Part 11-A: 점화 관계의 응용 (Applications of Recurrence Relations) — 기초편

> **Rosen 이산수학 8판 · Section 8.1 기반**
> 『Mathematics in Lean』 + Lean 4 공식화

---

## 0. 들어가며: 이 파트에서 배울 것

이 파트에서는 **점화 관계**(recurrence relation)의 세계에 발을 들여놓는다. 점화 관계란 수열의 다음 항을 이전 항들로 표현하는 규칙이다. 중학교 수학에서 "다음 수는 앞의 두 수를 더한 것"이라고 말하면, 그것이 바로 점화 관계이다!

이 파트에서는 다음을 다룬다:

1. **점화 관계란 무엇인가** — 직관적 이해부터 Lean 4 정의까지
2. **피보나치 수열** — 가장 유명한 점화 관계
3. **하노이 탑** — 고전적 퍼즐을 점화 관계로 모델링
4. Lean 4에서 **재귀 함수**(recursive function) 정의하기
5. **수학적 귀납법**(mathematical induction)으로 점화 관계의 성질 증명하기

### 이 파트에서 사용하는 핵심 Lean 4 개념

| 개념 | 설명 |
|------|------|
| `def f : ℕ → ℕ` | 재귀 함수 정의 |
| `induction n with` | 수학적 귀납법 |
| `rw`, `simp` | 재작성(rewriting) 전술 |
| `omega` | 자연수/정수 부등식 자동 증명 |
| `ring` | 대수적 항등식 자동 증명 |
| `calc` | 계산 증명 체인 |

---

## 1. 점화 관계란 무엇인가?

### 1.1 직관적 이해

**점화 관계**(recurrence relation)란 수열의 각 항을 그 **이전 항들의 함수**로 나타내는 등식이다.

쉽게 말해서, "다음 값을 구하려면 이전 값을 어떻게 조합하면 되는지" 알려주는 **레시피**(recipe)이다.

**일상적 예시**: 은행에 100만 원을 넣고 매년 5% 이자가 붙는다고 하자.

- 0년 후: 100만 원
- 1년 후: 100 × 1.05 = 105만 원
- 2년 후: 105 × 1.05 = 110.25만 원
- ...

이것을 수식으로 쓰면 `aₙ = 1.05 × aₙ₋₁` 이다. 이것이 바로 점화 관계이다!

### 1.2 형식적 정의

> **정의**: 수열 `{aₙ}`에 대한 **점화 관계**(recurrence relation)란 `n`이 어떤 값 이상일 때
> `aₙ`을 이전 항 `aₙ₋₁, aₙ₋₂, ..., a₀` 중 하나 이상으로 표현하는 등식이다.

점화 관계만으로는 수열이 유일하게 결정되지 않는다. **초기조건**(initial conditions)이 있어야 수열이 확정된다.

**비유**: 점화 관계는 "레시피"이고, 초기조건은 "재료"이다. 레시피(점화 관계)가 같아도 재료(초기조건)가 다르면 결과가 달라진다!

### 1.3 Lean 4에서의 표현

Lean 4에서 점화 관계는 **재귀 함수**(recursive function)로 자연스럽게 표현된다. Lean 4의 패턴 매칭(pattern matching)을 사용하면, 수학에서의 점화 관계를 거의 그대로 코드로 옮길 수 있다.

```lean
-- 가장 기본적인 점화 관계: aₙ = 2 * aₙ₋₁, a₀ = 1
-- 이것은 2의 거듭제곱을 생성한다: 1, 2, 4, 8, 16, ...
def powersOfTwo : ℕ → ℕ
  | 0     => 1           -- 초기조건: a₀ = 1
  | n + 1 => 2 * powersOfTwo n  -- 점화 관계: aₙ₊₁ = 2 * aₙ
```

여기서 핵심을 짚고 넘어가자:

- `| 0 => 1`은 **초기조건**(initial condition)이다. "n = 0일 때 값은 1"이라는 뜻이다.
- `| n + 1 => 2 * powersOfTwo n`은 **점화 관계**(recurrence relation)이다. "`n + 1`번째 값은 `n`번째 값의 2배"라는 뜻이다.
- Lean 4는 이 정의가 **종료**(termination)된다는 것을 자동으로 확인한다. `n + 1`에서 `n`으로 인수가 줄어들기 때문이다.

```lean
-- 값을 계산해보자
#eval powersOfTwo 0   -- 1
#eval powersOfTwo 5   -- 32
#eval powersOfTwo 10  -- 1024
```

---

## 2. lemma(작은 정리)와 theorem(큰 정리)의 관계

Lean 4 코드를 읽다 보면 `lemma`와 `theorem`이라는 두 가지 키워드가 나온다. 이 둘의 차이를 확실히 이해하고 넘어가자.

### 2.1 수학에서의 관계

수학에서 **정리**(theorem)와 **보조정리**(lemma)는 모두 "증명된 참인 명제"이다. 차이는 **역할**에 있다:

| 구분 | **정리**(theorem) | **보조정리**(lemma) |
|------|----------------|-----------------|
| 역할 | 그 자체로 중요한 결과 | 정리를 증명하기 위한 중간 단계 |
| 비유 | 완성된 건물 | 건물을 짓기 위한 벽돌 |
| 예시 | "피보나치 수의 명시적 공식" | "연속 피보나치 수는 서로소이다" |

**비유**: 큰 건물(theorem)을 지으려면 먼저 벽돌(lemma)을 하나하나 쌓아야 한다. 벽돌 자체는 "이게 멋지다!"라고 감탄할 일은 아니지만, 없으면 건물을 지을 수 없다.

### 2.2 Lean 4에서의 관계

Lean 4에서 `lemma`와 `theorem`은 **기술적으로 완전히 동일**하다! 둘 다 명제를 증명하는 데 사용된다.

```lean
-- 이 두 선언은 기능적으로 완전히 같다
lemma my_lemma : 1 + 1 = 2 := by omega
theorem my_theorem : 1 + 1 = 2 := by omega
```

차이는 순전히 **의미론적**(semantic)이다. 즉, 코드를 읽는 사람에게 "이것은 중간 단계입니다" 또는 "이것은 핵심 결과입니다"라는 **의도를 전달**하기 위한 것이다.

**실전 규칙**: 다른 증명에서 보조적으로 사용될 사실은 `lemma`로, 최종적으로 보여주고 싶은 결과는 `theorem`으로 쓰는 것이 관례이다.

---

## 3. if(→)와 if and only if(↔)의 차이

Lean 4에서 논리적 연결사를 정확히 이해하는 것은 매우 중요하다.

### 3.1 직관적 비교

| 기호 | 읽는 법 | 뜻 | 비유 |
|------|--------|------|------|
| `→` | "이면" (implies) | A가 참이면 B도 참 | 일방통행 도로 |
| `↔` | "일 때 그리고 그때에만" (if and only if) | A가 참이면 B도 참, B가 참이면 A도 참 | 양방통행 도로 |

### 3.2 구체적 예시

**→ (한 방향만 참)**:
"비가 오면 길이 젖는다" — 참이다.
하지만 "길이 젖으면 비가 온다"는 거짓일 수 있다 (누가 물을 뿌렸을 수도 있다).

**↔ (양 방향 모두 참)**:
"n이 짝수이다 ↔ n을 2로 나누면 나머지가 0이다" — 양쪽 모두 참이다.

### 3.3 Lean 4에서의 사용

```lean
-- → (implies): 한 방향
example (h : n > 5) : n > 3 := by omega

-- ↔ (iff): 양 방향
-- 증명하려면 두 방향을 각각 보여야 한다
example : n > 0 ↔ n ≠ 0 := by
  constructor        -- 두 방향으로 분리
  · intro h          -- (→) 방향: n > 0이면 n ≠ 0
    omega
  · intro h          -- (←) 방향: n ≠ 0이면 n > 0
    omega
```

`↔`는 `→`를 **두 번** 증명하는 것과 같다. Lean 4에서 `constructor` 전술로 양 방향을 분리한다.

**핵심 포인트**: `↔`로 증명된 것은 `rw`(재작성)로 양쪽을 자유롭게 바꿀 수 있어서 매우 편리하다!

---

## 4. 치환/대입 = 슈퍼포지션(Superposition)

### 4.1 치환이란?

**치환**(substitution) 또는 **대입**이란, 수식에서 어떤 변수를 다른 값이나 식으로 바꾸는 것이다.

예: `aₙ = 2aₙ₋₁ + 1`에서 `n` 자리에 `3`을 넣으면 → `a₃ = 2a₂ + 1`

이것은 Lean 4에서 매우 자연스럽다. 함수에 값을 넣는 것이 곧 치환이기 때문이다!

### 4.2 Lean 4에서의 치환

```lean
-- rw (rewrite) 전술이 바로 "치환"이다!
-- h : a = b 를 가지고 있으면, 목표에서 a를 b로 바꿀 수 있다
example (a b c : ℕ) (h : a = b) (h2 : b + c = 10) : a + c = 10 := by
  rw [h]      -- 목표의 a를 b로 치환 → b + c = 10
  exact h2    -- h2와 동일해짐

-- subst 전술: 변수를 완전히 제거하는 치환
example (a b : ℕ) (h : a = b) (h2 : b > 5) : a > 5 := by
  subst h     -- a를 b로 완전히 대체
  exact h2
```

### 4.3 점화 관계에서의 치환

점화 관계의 닫힌 형태(closed form)를 증명할 때, 치환은 핵심 도구이다:

```lean
-- powersOfTwo n = 2^n 을 증명할 때
-- 귀납 단계에서 ih : powersOfTwo n = 2^n 라는 가정을
-- powersOfTwo (n+1) = 2 * powersOfTwo n 에 치환한다
-- → powersOfTwo (n+1) = 2 * 2^n = 2^(n+1)
```

---

## 5. 피보나치 수열 — 가장 유명한 점화 관계

### 5.1 역사적 배경

**피보나치 수열**(Fibonacci sequence)은 1202년 이탈리아 수학자 **레오나르도 피보나치**(Leonardo di Pisa, 피보나치라는 별명으로 더 유명하다)가 그의 저서 『Liber Abaci』에서 토끼 번식 문제를 통해 소개하였다.

**문제**: 한 쌍의 어린 토끼가 섬에 있다. 토끼는 태어난 지 2개월이 되면 매달 한 쌍의 새끼를 낳는다. 토끼는 죽지 않는다고 가정할 때, n개월 후 토끼 쌍의 수는?

이 문제를 풀면 수열 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, ... 가 나온다. 이것이 바로 피보나치 수열이다!

### 5.2 점화 관계로 표현

피보나치 수열 `{fₙ}`은 다음과 같이 정의된다:

- **초기조건**: `f₀ = 0`, `f₁ = 1`
- **점화 관계**: `fₙ = fₙ₋₁ + fₙ₋₂` (n ≥ 2)

수열의 처음 몇 항을 나열하면:

| n | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| fₙ | 0 | 1 | 1 | 2 | 3 | 5 | 8 | 13 | 21 | 34 | 55 |

### 5.3 Lean 4에서의 피보나치 정의

Lean 4에서 피보나치 수열은 패턴 매칭을 이용하여 아주 자연스럽게 정의할 수 있다:

```lean
-- 피보나치 수열 정의
-- @[simp]는 simp 전술이 이 정의를 자동으로 사용하게 한다
@[simp] def fib : ℕ → ℕ
  | 0     => 0              -- f₀ = 0
  | 1     => 1              -- f₁ = 1
  | n + 2 => fib n + fib (n + 1)  -- fₙ₊₂ = fₙ + fₙ₊₁
```

**코드 해설**:

1. `@[simp]` — 이 **속성**(attribute)은 `simp` 전술에게 "이 함수의 정의 등식을 자동으로 사용해도 좋다"고 알려준다.
2. `def fib : ℕ → ℕ` — 자연수를 받아 자연수를 돌려주는 함수를 정의한다.
3. `| 0 => 0` — 패턴 매칭: 입력이 0이면 0을 반환한다.
4. `| 1 => 1` — 패턴 매칭: 입력이 1이면 1을 반환한다.
5. `| n + 2 => fib n + fib (n + 1)` — 입력이 `n + 2` 형태이면 **재귀적으로** `fib n`과 `fib (n + 1)`을 더한다.

Lean 4는 인수가 `n + 2`에서 `n`과 `n + 1`로 줄어드는 것을 확인하여 이 재귀가 반드시 끝난다는 것을 자동으로 보장한다.

```lean
-- 값 확인
#eval fib 0   -- 0
#eval fib 1   -- 1
#eval fib 6   -- 8
#eval fib 10  -- 55

-- 처음 20개 피보나치 수 한 번에 보기
#eval List.range 20 |>.map fib
-- [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, ...]
```

### 5.4 fib의 정의 등식 활용

fib의 정의 자체가 세 개의 등식을 제공한다. 이를 증명에서 직접 활용할 수 있다:

```lean
-- 이 세 등식은 정의에 의해 자동으로 성립 (rfl로 증명 가능)
example : fib 0 = 0 := rfl
example : fib 1 = 1 := rfl

-- n + 2 케이스는 이름을 붙여두면 편리하다
theorem fib_add_two (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) := rfl
```

`rfl`은 "reflexivity(반사성)"의 약자로, 양변이 **정의에 의해 동일할 때** 사용한다. 점화 관계의 정의 등식은 항상 `rfl`로 증명할 수 있다!

---

## 6. 첫 번째 증명: 피보나치 수열의 기본 성질

### 6.1 연속 피보나치 수의 합

**정리**: `fib 0 + fib 1 + fib 2 + ... + fib n = fib (n + 2) - 1`

이 정리를 증명하기 전에, 먼저 **아주 간단한** 성질부터 증명해보자.

### 6.2 예제: fib (n + 2) ≥ 1

**주장**: 모든 자연수 n에 대해 `fib (n + 2) ≥ 1`이다.

**증명 전략**: 수학적 귀납법을 사용한다.
- **기저 사례**(base case): `fib 2 = fib 0 + fib 1 = 0 + 1 = 1 ≥ 1` ✓
- **귀납 단계**(inductive step): `fib (n + 2) ≥ 1`이면 `fib (n + 3) = fib (n + 1) + fib (n + 2) ≥ 0 + 1 = 1` ✓

```lean
-- 완전한 증명
theorem fib_succ_succ_pos (n : ℕ) : fib (n + 2) ≥ 1 := by
  induction n with
  | zero =>
    -- 기저: fib 2 = fib 0 + fib 1 = 0 + 1 = 1
    simp [fib]
  | succ n ih =>
    -- 귀납: fib (n + 3) = fib (n + 1) + fib (n + 2)
    -- ih : fib (n + 2) ≥ 1
    rw [fib_add_two]
    -- fib (n + 1) + fib (n + 2) ≥ 0 + 1 = 1
    omega
```

**코드를 한 줄 한 줄 뜯어보자:**

1. `induction n with` — n에 대해 수학적 귀납법을 시작한다. `with`로 각 케이스에 이름을 붙인다.
2. `| zero =>` — 기저 사례 (n = 0). 이때 증명할 것은 `fib 2 ≥ 1`이다.
3. `simp [fib]` — `fib`의 정의를 펼쳐서 `1 ≥ 1`로 단순화한 뒤 자동 증명한다.
4. `| succ n ih =>` — 귀납 단계. `n`이 귀납 변수, `ih`가 귀납 가정이다.
5. `rw [fib_add_two]` — `fib (n + 3)`을 `fib (n + 1) + fib (n + 2)`로 재작성한다.
6. `omega` — 자연수 부등식을 자동으로 해결한다. `ih`에서 `fib (n + 2) ≥ 1`을 알고 있으므로 합도 `≥ 1`임을 알 수 있다.

---

## 7. 연습 문제 — 레벨 1: 괄호 채우기

이제 직접 해볼 차례이다! 아래 코드에서 `{! !}` 부분을 채워보자. (실제 Lean 4에서는 `sorry`로 표시된 부분을 완성하면 된다.)

### 연습 7.1: 간단한 점화 관계 정의

2의 거듭제곱 수열을 점화 관계로 정의하라.

```lean
-- 연습: 빈칸을 채우시오
def powTwo : ℕ → ℕ
  | 0     => {① 초기값}
  | n + 1 => {② 점화 관계}
```

<details>
<summary>💡 답 보기</summary>

```lean
def powTwo : ℕ → ℕ
  | 0     => 1             -- ① 2⁰ = 1
  | n + 1 => 2 * powTwo n  -- ② 2^(n+1) = 2 · 2^n
```

**설명**: `powTwo 0 = 1` (2⁰ = 1)이고, `powTwo (n+1) = 2 * powTwo n` (2^(n+1) = 2 · 2^n)이다.
</details>

### 연습 7.2: 피보나치 값 계산

다음 피보나치 수의 값을 Lean 4로 증명하라.

```lean
-- fib 7의 값을 증명하라
example : fib 7 = {③ 값} := by {④ 전술}
```

<details>
<summary>💡 답 보기</summary>

```lean
example : fib 7 = 13 := by native_decide
-- 또는
example : fib 7 = 13 := by decide
-- 또는 그냥
example : fib 7 = 13 := rfl
```

**설명**: `fib 7 = fib 5 + fib 6 = 5 + 8 = 13`이다. Lean 4는 계산 가능한 등식을 `native_decide`, `decide`, 또는 `rfl`로 증명할 수 있다.
</details>

### 연습 7.3: 귀납법 기저 사례

다음 증명에서 기저 사례를 완성하라.

```lean
-- 모든 n에 대해 fib n ≤ fib (n + 1) 임을 보여라
theorem fib_le_fib_succ : ∀ n : ℕ, fib n ≤ fib (n + 1) := by
  intro n
  induction n with
  | zero =>
    -- 목표: fib 0 ≤ fib 1, 즉 0 ≤ 1
    {⑤ 기저 사례 증명}
  | succ n ih =>
    -- ih : fib n ≤ fib (n + 1)
    -- 목표: fib (n + 1) ≤ fib (n + 2)
    rw [fib_add_two]
    omega
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem fib_le_fib_succ : ∀ n : ℕ, fib n ≤ fib (n + 1) := by
  intro n
  induction n with
  | zero =>
    simp [fib]          -- ⑤ fib 0 = 0, fib 1 = 1이므로 0 ≤ 1
  | succ n ih =>
    rw [fib_add_two]
    omega
```

**설명**: 기저 사례에서 `fib 0 = 0`이고 `fib 1 = 1`이므로 `0 ≤ 1`은 자명하다. `simp [fib]`가 fib의 정의를 펼쳐서 자동 처리한다.
</details>

---

## 8. 하노이 탑 — 고전적 퍼즐

### 8.1 문제 소개

**하노이 탑**(Tower of Hanoi)은 19세기 프랑스의 수학자 에두아르 루카스(Édouard Lucas)가 고안한 퍼즐이다.

**규칙**:
- 세 개의 기둥이 있다.
- 기둥 1에 크기가 다른 n개의 원반이 크기순으로 놓여 있다 (가장 큰 것이 아래).
- 원반을 한 번에 하나씩 이동할 수 있다.
- 작은 원반 위에 큰 원반을 놓을 수 없다.
- 모든 원반을 기둥 2로 옮기는 것이 목적이다.

**질문**: n개의 원반을 옮기는 데 필요한 **최소 이동 횟수** `Hₙ`은?

### 8.2 점화 관계 도출

이동 전략을 생각해보자:

1. 위의 `n - 1`개 원반을 기둥 3으로 옮긴다 → `Hₙ₋₁`번 이동
2. 가장 큰 원반을 기둥 2로 옮긴다 → 1번 이동
3. 기둥 3의 `n - 1`개 원반을 기둥 2로 옮긴다 → `Hₙ₋₁`번 이동

따라서:
- **초기조건**: `H₁ = 1` (원반 1개는 1번만 옮기면 된다)
- **점화 관계**: `Hₙ = 2Hₙ₋₁ + 1` (n ≥ 2)

### 8.3 Lean 4에서의 정의

```lean
-- 하노이 탑: n개 원반을 옮기는 최소 이동 횟수
def hanoi : ℕ → ℕ
  | 0     => 0              -- 원반 0개: 이동 불필요
  | n + 1 => 2 * hanoi n + 1  -- Hₙ₊₁ = 2·Hₙ + 1

-- 값 확인
#eval hanoi 1   -- 1
#eval hanoi 2   -- 3
#eval hanoi 3   -- 7
#eval hanoi 4   -- 15
#eval hanoi 10  -- 1023
#eval hanoi 64  -- 18446744073709551615 (약 1.8 × 10¹⁹)
```

패턴이 보이는가? `hanoi n = 2ⁿ - 1`인 것 같다!

### 8.4 닫힌 공식 증명: hanoi n = 2ⁿ - 1

점화 관계의 **닫힌 형태**(closed form)란, 이전 항을 참조하지 않고 `n`만으로 값을 바로 구할 수 있는 공식이다.

`hanoi n = 2ⁿ - 1`을 증명해보자. 단, 자연수에서는 뺄셈이 까다로우므로 (0 - 1 = 0이 되어버린다), 양변에 1을 더한 형태로 증명하는 것이 더 깔끔하다:

**목표**: `hanoi n + 1 = 2ⁿ`

```lean
-- 하노이 탑의 닫힌 공식
theorem hanoi_eq (n : ℕ) : hanoi n + 1 = 2 ^ n := by
  induction n with
  | zero =>
    -- 기저: hanoi 0 + 1 = 2⁰ = 1
    -- hanoi 0 = 0이므로 0 + 1 = 1 ✓
    simp [hanoi]
  | succ n ih =>
    -- 귀납 가정 ih : hanoi n + 1 = 2^n
    -- 목표: hanoi (n + 1) + 1 = 2^(n + 1)
    simp [hanoi]        -- hanoi (n+1) = 2 * hanoi n + 1 펼침
    -- 목표: 2 * hanoi n + 1 + 1 = 2^(n+1)
    -- ih에서 hanoi n = 2^n - 1 이므로
    -- 2 * (2^n - 1) + 1 + 1 = 2^(n+1)
    -- 2^(n+1) - 2 + 2 = 2^(n+1) ✓
    rw [pow_succ]       -- 2^(n+1) = 2^n * 2
    omega               -- 나머지 산술은 omega가 처리
```

**증명 과정 상세 해설**:

1. `induction n with` — n에 대한 수학적 귀납법을 시작한다.

2. 기저 사례 (`n = 0`):
   - 증명할 것: `hanoi 0 + 1 = 2^0`
   - `hanoi 0 = 0` (정의에 의해)이므로 `0 + 1 = 1`
   - `2^0 = 1`이므로 `1 = 1` ✓

3. 귀납 단계 (`n → n + 1`):
   - 귀납 가정: `hanoi n + 1 = 2^n`
   - 증명할 것: `hanoi (n + 1) + 1 = 2^(n+1)`
   - `hanoi (n + 1) = 2 * hanoi n + 1`이므로
   - `(2 * hanoi n + 1) + 1 = 2^(n+1)`
   - `2 * hanoi n + 2 = 2^(n+1)`
   - 귀납 가정에서 `hanoi n = 2^n - 1`이므로
   - `2 * (2^n - 1) + 2 = 2^(n+1) - 2 + 2 = 2^(n+1)` ✓

---

## 9. 연습 문제 — 레벨 2: skeleton 채우기

### 연습 9.1: 하노이 탑 값 확인

```lean
-- hanoi 5 = 31 임을 증명하라
example : hanoi 5 = {⑥ 값} := by {⑦ 전술}
```

<details>
<summary>💡 답 보기</summary>

```lean
example : hanoi 5 = 31 := by native_decide
```
</details>

### 연습 9.2: 3의 거듭제곱 점화 관계

```lean
-- 3의 거듭제곱 수열 정의
def powThree : ℕ → ℕ
  | 0     => 1
  | n + 1 => 3 * powThree n

-- powThree n = 3^n 임을 증명하라
theorem powThree_eq (n : ℕ) : powThree n = 3 ^ n := by
  induction n with
  | zero =>
    {⑧ 기저 사례}
  | succ n ih =>
    {⑨ 귀납 단계}
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem powThree_eq (n : ℕ) : powThree n = 3 ^ n := by
  induction n with
  | zero =>
    simp [powThree]       -- ⑧ powThree 0 = 1 = 3^0
  | succ n ih =>
    simp [powThree]       -- ⑨ powThree (n+1) = 3 * powThree n
    rw [ih]               --    = 3 * 3^n
    ring                  --    = 3^(n+1)
```

**설명**: 귀납 단계에서 `simp [powThree]`로 정의를 펼치고, `rw [ih]`로 귀납 가정을 대입한 후, `ring`으로 `3 * 3^n = 3^(n+1)`을 자동 증명한다.
</details>

### 연습 9.3: 2의 거듭제곱 점화 관계 (전체 증명)

```lean
-- 모든 것을 처음부터 채워보자
def powTwo' : ℕ → ℕ
  | 0     => 1
  | n + 1 => 2 * powTwo' n

theorem powTwo'_eq (n : ℕ) : powTwo' n = 2 ^ n := by
  {⑩ 전체 증명을 작성하라}
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem powTwo'_eq (n : ℕ) : powTwo' n = 2 ^ n := by
  induction n with
  | zero => simp [powTwo']
  | succ n ih =>
    simp [powTwo']
    rw [ih]
    ring
```
</details>

---

## 10. 비트 스트링과 점화 관계 (Rosen 예제 3)

### 10.1 문제

**문제**: 두 개의 연속된 0을 갖지 않는 길이 n의 **비트 스트링**(bit string)의 수에 대한 점화 관계를 구하라.

이것은 Rosen 교재 8.1절의 예제 3이다.

### 10.2 분석

`aₙ`을 두 개의 연속된 0을 갖지 않는 길이 n의 비트 스트링의 수라 하자.

길이 n의 유효한 비트 스트링은 두 종류로 나뉜다:
- **1로 끝나는 경우**: 앞의 n-1개는 유효한 비트 스트링이면 된다 → `aₙ₋₁`가지
- **0으로 끝나는 경우**: 바로 앞 비트는 반드시 1이어야 한다 (연속 0 금지). 그러면 앞의 n-2개는 유효한 비트 스트링이면 된다 → `aₙ₋₂`가지

따라서: **`aₙ = aₙ₋₁ + aₙ₋₂`** (피보나치와 같은 점화 관계!)

초기조건:
- `a₁ = 2` (0, 1)
- `a₂ = 3` (01, 10, 11)

### 10.3 Lean 4로 모델링

```lean
-- 두 개의 연속된 0이 없는 길이 n의 비트 스트링 수
def validBitStrings : ℕ → ℕ
  | 0     => 1    -- 빈 문자열 1개 (관례상)
  | 1     => 2    -- "0", "1"
  | n + 2 => validBitStrings (n + 1) + validBitStrings n

-- 실제로 피보나치와 관계가 있다: aₙ = fib(n + 2)
-- a₁ = 2 = fib 3, a₂ = 3 = fib 4, a₃ = 5 = fib 5, ...
#eval List.range 8 |>.map validBitStrings
-- [1, 2, 3, 5, 8, 13, 21, 34]
#eval List.range 8 |>.map (fun n => fib (n + 2))
-- [1, 2, 3, 5, 8, 13, 21, 34]
```

### 10.4 피보나치 수열과의 관계 증명

```lean
-- validBitStrings n = fib (n + 2) 임을 증명
theorem validBitStrings_eq_fib (n : ℕ) :
    validBitStrings n = fib (n + 2) := by
  induction n with
  | zero => simp [validBitStrings, fib]
  | succ n ih =>
    cases n with
    | zero => simp [validBitStrings, fib]
    | succ n =>
      simp only [validBitStrings]
      rw [ih]
      -- 이전 항도 치환 필요
      sorry -- 완전한 증명은 연습 문제로!
```

---

## 11. 연습 문제 — 레벨 3: sorry 채우기 (독립 증명)

이제 `sorry`를 제거하고 완전한 증명을 작성해보자. 이것은 가장 도전적인 단계이다!

### 연습 11.1: 등차수열의 점화 관계

```lean
-- 등차수열: aₙ = a₀ + n * d
-- 점화 관계: aₙ₊₁ = aₙ + d
def arithSeq (a₀ d : ℕ) : ℕ → ℕ
  | 0     => a₀
  | n + 1 => arithSeq a₀ d n + d

-- 닫힌 공식 증명: arithSeq a₀ d n = a₀ + n * d
theorem arithSeq_closed (a₀ d : ℕ) (n : ℕ) :
    arithSeq a₀ d n = a₀ + n * d := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem arithSeq_closed (a₀ d : ℕ) (n : ℕ) :
    arithSeq a₀ d n = a₀ + n * d := by
  induction n with
  | zero => simp [arithSeq]
  | succ n ih =>
    simp [arithSeq]
    rw [ih]
    ring
```

**설명**: 
- 기저: `arithSeq a₀ d 0 = a₀ = a₀ + 0 * d`
- 귀납: `arithSeq a₀ d (n+1) = arithSeq a₀ d n + d = (a₀ + n*d) + d = a₀ + (n+1)*d`
</details>

### 연습 11.2: 등비수열의 점화 관계

```lean
-- 등비수열: aₙ = a₀ * rⁿ
-- 점화 관계: aₙ₊₁ = r * aₙ
def geomSeq (a₀ r : ℕ) : ℕ → ℕ
  | 0     => a₀
  | n + 1 => r * geomSeq a₀ r n

-- 닫힌 공식: geomSeq a₀ r n = a₀ * r^n
theorem geomSeq_closed (a₀ r : ℕ) (n : ℕ) :
    geomSeq a₀ r n = a₀ * r ^ n := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem geomSeq_closed (a₀ r : ℕ) (n : ℕ) :
    geomSeq a₀ r n = a₀ * r ^ n := by
  induction n with
  | zero => simp [geomSeq]
  | succ n ih =>
    simp [geomSeq]
    rw [ih]
    ring
```
</details>

### 연습 11.3: 연속 피보나치 수의 서로소 (도전!)

이 문제는 Mathematics in Lean에서 나온 것이다. 연속하는 두 피보나치 수는 항상 서로소이다.

```lean
-- Mathlib의 Nat.Coprime를 사용한다
-- Nat.Coprime a b는 Nat.gcd a b = 1 이라는 뜻이다

-- 연속 피보나치 수는 서로소
theorem fib_coprime_fib_succ (n : ℕ) :
    Nat.Coprime (fib n) (fib (n + 1)) := by
  sorry
```

<details>
<summary>💡 힌트</summary>

`Nat.coprime_add_self_right`를 사용하라. 이것은 `Nat.Coprime a b → Nat.Coprime a (b + a)`를 의미한다. 귀납법에서 `ih.symm`을 사용하여 `Coprime (fib (n+1)) (fib n)`에서 `Coprime (fib n) (fib (n+1))`로 바꿀 수 있다.
</details>

<details>
<summary>💡 답 보기</summary>

```lean
theorem fib_coprime_fib_succ (n : ℕ) :
    Nat.Coprime (fib n) (fib (n + 1)) := by
  induction n with
  | zero => simp [fib, Nat.Coprime]
  | succ n ih =>
    simp only [fib_add_two, Nat.coprime_add_self_right]
    exact ih.symm
```

**설명**: 
- 기저 (n = 0): `gcd(fib 0, fib 1) = gcd(0, 1) = 1` ✓
- 귀납 단계: 
  - `ih : Coprime (fib n) (fib (n + 1))`
  - 목표: `Coprime (fib (n+1)) (fib (n+2))`
  - `fib (n+2) = fib n + fib (n+1)`이므로
  - `Coprime (fib (n+1)) (fib n + fib (n+1))`
  - `coprime_add_self_right`에 의해 `Coprime (fib (n+1)) (fib n)`이면 충분
  - `ih.symm`이 바로 이것!
</details>

---

## 12. 사용된 Lean 4 전술 정리

| 전술 | 용도 | 예시 |
|------|------|------|
| `induction n with` | 자연수 귀납법 | `induction n with \| zero => ... \| succ n ih => ...` |
| `rfl` | 정의에 의한 등식 | `example : fib 0 = 0 := rfl` |
| `simp [f]` | 함수 정의를 펼쳐서 단순화 | `simp [fib]` |
| `rw [h]` | 등식 h를 이용한 재작성(치환) | `rw [fib_add_two]` |
| `ring` | 대수적 항등식 자동 증명 | `3 * 3^n = 3^(n+1)` |
| `omega` | 자연수/정수 산술 자동 | `2 * a + 2 ≥ 2` |
| `constructor` | ∧, ↔ 분리 | `constructor; intro h; ...` |
| `exact h` | 가정 h로 목표 완성 | `exact ih.symm` |
| `native_decide` | 계산 가능한 명제 판정 | `fib 10 = 55` |
| `pow_succ` | `a^(n+1) = a^n * a` | `rw [pow_succ]` |

---

## 13. 핵심 요약

1. **점화 관계**(recurrence relation)는 수열의 각 항을 이전 항들로 표현하는 규칙이다.
2. 점화 관계를 유일하게 결정하려면 **초기조건**(initial conditions)이 필요하다.
3. Lean 4에서 점화 관계는 **재귀 함수**로 자연스럽게 정의된다.
4. **수학적 귀납법**으로 점화 관계의 성질(닫힌 공식 등)을 증명한다.
5. `lemma`는 보조 단계, `theorem`은 핵심 결과를 나타내지만, Lean 4에서는 기능적으로 동일하다.
6. `→`는 "이면" (한 방향), `↔`는 "일 때 그리고 그때에만" (양 방향)이다.
7. **치환**(substitution)은 `rw` 전술로 수행되며, 이것이 증명의 핵심 도구이다.

---

> **다음 파트 예고**: Part 11-B에서는 **선형 점화 관계**(linear recurrence relations)를 다룬다. 특성 방정식(characteristic equation)을 사용하여 점화 관계의 일반항을 구하는 체계적인 방법을 배운다. 피보나치 수열의 명시적 공식(Binet's formula)도 증명한다!
