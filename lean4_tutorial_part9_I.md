# 📘 Lean 4 튜토리얼 — Part 9-I: 정리의 세계로 — lemma, theorem, →, ↔, 그리고 치환

> **『Mathematics in Lean』 Chapter 2~3 기반 · Rosen 이산수학과 연결**
> 이전 파트(Part 9-A~H)에서 이산수학의 계수(counting) 문제를 Lean 4로 다루었다.
> 이번 파트에서는 한 발 뒤로 물러서서, Lean 4에서 **정리**(theorem)란 무엇이고,
> **증명**(proof)이 어떻게 작동하는지를 **가장 기초부터** 차근차근 올라간다.
> 이론을 아예 모르는 중학생도 따라올 수 있도록 **매우 자세하게** 설명한다.

---

## 🎯 이 파트에서 배울 것

| 순서 | 주제 | 핵심 질문 |
|------|------|----------|
| 9I.1 | 정리란 무엇인가? | "정리 = 타입, 증명 = 값"이라는 Lean의 철학 |
| 9I.2 | **작은 정리**(lemma)와 **큰 정리**(theorem) | 뭐가 다르고, 왜 나눌까? |
| 9I.3 | **치환/대입**(rewriting = 슈퍼포지션) | `rw` 전술의 정체 |
| 9I.4 | **함의**(→, implication = "만약 ~이면") | `intro`, `apply` 전술 |
| 9I.5 | **동치**(↔, iff = "~일 때 그리고 그때에만") | `constructor`, `.mp`, `.mpr` |
| 9I.6 | → 와 ↔ 의 차이 한눈에 보기 | 일방통행 vs 양방향 |
| 9I.7 | `calc` — 계산풍 증명 | 한 줄씩 따라가는 증명 |
| 9I.8 | 종합 연습 | 위의 모든 것을 한꺼번에 |

---

## 9I.0 시작하기 전에 — 용어 정리

Lean 4를 처음 보는 독자를 위해, 앞으로 계속 나올 핵심 용어를 먼저 정리한다.

| 한국어 | 영어 | Lean 4에서의 모습 | 쉬운 비유 |
|--------|------|------------------|----------|
| **정리**(theorem) | theorem | `theorem 이름 : 명제 := 증명` | "수학에서 증명된 사실" |
| **보조정리**(lemma) | lemma | `lemma 이름 : 명제 := 증명` | "큰 정리를 위한 디딤돌" |
| **명제**(proposition) | Prop | `2 + 3 = 5`, `∀ n, 0 ≤ n` | "참/거짓을 판별할 수 있는 문장" |
| **증명**(proof) | proof | `by rw [...]`, `by simp` | "명제가 참임을 보이는 근거" |
| **전술**(tactic) | tactic | `rw`, `apply`, `intro`, `simp` | "증명을 만드는 도구/명령어" |
| **가설**(hypothesis) | hypothesis | `h : a = b` | "이미 참이라고 알려진 사실" |
| **목표**(goal) | goal | `⊢ a + b = b + a` | "지금 증명해야 하는 것" |
| **치환**(rewriting) | rewriting | `rw [h]` | "같은 것으로 바꿔치기" |
| **함의**(implication) | → | `P → Q` | "P이면 Q이다" (일방통행) |
| **동치**(iff) | ↔ | `P ↔ Q` | "P이면 Q, Q이면 P" (양방향) |

---

## 9I.1 정리란 무엇인가? — "정리 = 타입, 증명 = 값"

### 🤔 중학교 수학에서의 정리

중학교에서 배우는 "피타고라스의 정리"를 떠올려 보자.

> **정리**: 직각삼각형에서 빗변의 제곱은 나머지 두 변의 제곱의 합과 같다.

이 정리는 두 부분으로 이루어져 있다:
1. **주장**(statement): "빗변² = 밑변² + 높이²"
2. **증명**(proof): 왜 이것이 참인지 보여주는 논증

### 🖥️ Lean 4에서의 정리

Lean 4에서도 **똑같은 구조**이다!

```lean
-- 주장(statement)     증명(proof)
--    ↓                   ↓
theorem my_first : 2 + 3 = 5 := by norm_num
```

- `theorem` : "이것은 정리입니다"라는 **키워드**(keyword)
- `my_first` : 이 정리에 붙인 **이름**
- `2 + 3 = 5` : 증명하려는 **명제**(proposition) — 이것이 **타입**(type)에 해당한다
- `:= by norm_num` : **증명** — 이것이 **값**(value)에 해당한다

#### 💡 핵심 아이디어: "명제 = 타입, 증명 = 값"

Lean 4의 가장 중요한 철학은 이것이다:

> **명제**(참/거짓을 판별할 수 있는 문장)는 **타입**(type)이고,
> **증명**(그 명제가 참임을 보이는 것)은 그 타입에 속하는 **값**(value)이다.

이것은 마치 "상자와 물건"에 비유할 수 있다:

```
타입(상자)         값(물건)
──────────        ──────────
Nat               0, 1, 2, 3, ...
String            "hello", "lean4", ...
2 + 3 = 5         (이 등식이 참이라는 증거)
```

`Nat`이라는 상자에 `0`, `1`, `2` 같은 자연수가 들어가듯이,
`2 + 3 = 5`라는 상자에는 "이것이 참이라는 증거"가 들어간다.
증거가 **하나라도 존재하면** 그 명제는 **참**이고,
증거가 **하나도 존재할 수 없으면** 그 명제는 **거짓**이다.

### 🔬 직접 확인하기

```lean
-- #check 명령어로 "이 녀석의 타입이 뭐지?"를 물어볼 수 있다
#check (2 : Nat)           -- 2 : Nat        ← "2는 자연수이다"
#check "hello"             -- "hello" : String
#check @rfl Nat 5          -- @rfl Nat 5 : 5 = 5  ← "5=5의 증거"

-- theorem도 #check로 볼 수 있다!
theorem five_eq : 2 + 3 = 5 := by norm_num
#check five_eq             -- five_eq : 2 + 3 = 5
-- ↑ "five_eq는 '2+3=5'라는 명제의 증거이다"
```

### ✏️ 연습 9I.1-a: 첫 번째 정리 완성하기 (괄호 채우기)

```lean
-- 3 × 4 = 12 임을 증명해 보자
theorem mul_example : 3 * 4 = 12 := by
  /-[ 여기를 채우세요 ]-/
```

<details>
<summary>💡 힌트</summary>

숫자 계산은 `norm_num` 전술이 자동으로 해결해준다.

</details>

<details>
<summary>✅ 답 보기</summary>

```lean
theorem mul_example : 3 * 4 = 12 := by
  norm_num
```

`norm_num`은 "숫자 관련 명제를 자동으로 증명하라"는 전술이다.
`2 + 3 = 5`, `7 < 10`, `15 ≠ 0` 같은 구체적 숫자 계산에 쓸 수 있다.

</details>

### ✏️ 연습 9I.1-b: 부등식 정리 (sorry 채우기)

```lean
-- 이번에는 부등식을 증명하자
theorem ineq_example : (7 : Nat) < 10 := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
theorem ineq_example : (7 : Nat) < 10 := by
  norm_num
```

`(7 : Nat)` 처럼 타입을 명시하면 Lean이 자연수 세계에서 비교하도록 알려줄 수 있다.

</details>

---

## 9I.2 작은 정리(lemma)와 큰 정리(theorem)의 관계

### 🏗️ 건물 비유

큰 건물을 지을 때, 벽돌 하나하나를 먼저 쌓아야 한다.
수학에서도 마찬가지이다:

```
        ┌─────────────────────┐
        │   큰 정리(theorem)    │  ← 완성된 건물
        └──────────┬──────────┘
                   │ 의존
        ┌──────────┴──────────┐
        │  보조정리 A(lemma)    │  ← 벽돌 1
        │  보조정리 B(lemma)    │  ← 벽돌 2
        │  보조정리 C(lemma)    │  ← 벽돌 3
        └─────────────────────┘
```

**보조정리**(lemma)는 그 자체로도 참인 사실이지만,
주로 **더 큰 정리를 증명하기 위한 디딤돌**로 사용된다.

### 🖥️ Lean 4에서 lemma와 theorem

Lean 4에서 `lemma`와 `theorem`은 **기능적으로 완전히 동일**하다!

```lean
-- 이 두 개는 Lean 4 내부적으로 완전히 같은 것이다:
lemma  helper : 1 + 1 = 2 := by norm_num
theorem result : 1 + 1 = 2 := by norm_num
```

그렇다면 왜 두 가지를 구분할까? 이유는 **의사소통**(communication)이다.

| 키워드 | 의미 | 언제 사용하는가 |
|--------|------|----------------|
| `lemma` | "이것은 디딤돌입니다" | 다른 정리를 증명하기 위한 보조 사실 |
| `theorem` | "이것은 목표입니다" | 최종적으로 보여주고 싶은 주요 결과 |

코드를 읽는 사람에게 **"이 사실은 보조적인 것이에요"** vs **"이 사실이 핵심이에요"**라는
신호를 보내는 것이다. 프로그래밍에서 함수 이름에 `_helper`를 붙이는 것과 비슷하다.

### 🔬 실전 예시: lemma를 써서 theorem 증명하기

```lean
-- 보조정리: 0은 모든 자연수 이하이다
lemma zero_le_any (n : Nat) : 0 ≤ n := Nat.zero_le n

-- 보조정리: 어떤 수에 0을 더해도 그 수이다
lemma add_zero_eq (n : Nat) : n + 0 = n := Nat.add_zero n

-- 큰 정리: 이 두 보조정리를 조합하여 증명
theorem zero_plus_zero_le (n : Nat) : 0 + 0 ≤ n := by
  rw [add_zero_eq 0]   -- "0 + 0"을 "0"으로 치환
  exact zero_le_any n   -- "0 ≤ n"은 이미 증명됨
```

여기서 핵심 패턴을 보자:

1. `lemma zero_le_any` — 디딤돌 ①
2. `lemma add_zero_eq` — 디딤돌 ②
3. `theorem zero_plus_zero_le` — 디딤돌 ①②를 **조합**하여 최종 결과를 얻음

### 📚 Mathlib(수학 라이브러리)에서의 실제 사용

Mathlib에서는 수천 개의 `lemma`가 정의되어 있고,
이들을 조합해서 `theorem`을 증명한다.
예를 들어, 소수의 무한성 증명에는 수십 개의 보조정리가 동원된다.

```lean
-- Mathlib에 실제로 있는 보조정리들의 예:
#check Nat.zero_le       -- lemma: 0 ≤ n
#check Nat.succ_le_succ  -- lemma: n ≤ m → n+1 ≤ m+1
#check Nat.lt_of_lt_of_le -- lemma: a < b → b ≤ c → a < c
```

### ✏️ 연습 9I.2-a: lemma와 theorem 만들기 (괄호 채우기)

```lean
-- 보조정리: n + 0 = n
lemma my_add_zero (n : Nat) : n + 0 = n := by
  /-[ 여기를 채우세요 ]-/

-- 큰 정리: (n + 0) + 0 = n (보조정리를 두 번 사용)
theorem my_double_zero (n : Nat) : (n + 0) + 0 = n := by
  rw [/-[ 여기를 채우세요 ]-/]
  rw [/-[ 여기를 채우세요 ]-/]
```

<details>
<summary>💡 힌트</summary>

- `my_add_zero`는 `omega` 또는 `simp`로 증명할 수 있다.
- `my_double_zero`에서는 `my_add_zero`를 `rw`로 사용한다.
  `rw [my_add_zero]`를 하면 `? + 0`을 `?`로 바꿔준다.

</details>

<details>
<summary>✅ 답 보기</summary>

```lean
lemma my_add_zero (n : Nat) : n + 0 = n := by
  omega

theorem my_double_zero (n : Nat) : (n + 0) + 0 = n := by
  rw [my_add_zero]    -- (n + 0) + 0 → n + 0
  rw [my_add_zero]    -- n + 0 → n
```

첫 번째 `rw [my_add_zero]`는 가장 바깥의 `? + 0`을 찾아서 `?`로 바꾼다.
그 결과 `n + 0 = n`이 남고, 두 번째 `rw [my_add_zero]`가 이것도 처리한다.

</details>

### ✏️ 연습 9I.2-b: 직접 lemma 만들어서 theorem 증명하기 (sorry)

```lean
-- 보조정리를 하나 만들어서 큰 정리를 증명하라
lemma my_mul_one (n : Nat) : n * 1 = n := by
  sorry

theorem my_combined (n : Nat) : n * 1 + 0 = n := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
lemma my_mul_one (n : Nat) : n * 1 = n := by
  omega

theorem my_combined (n : Nat) : n * 1 + 0 = n := by
  rw [my_mul_one]     -- n * 1 → n
  rw [Nat.add_zero]   -- n + 0 → n
  -- 또는 한 줄로: simp [my_mul_one]
```

</details>

---

## 9I.3 치환/대입 — `rw` 전술 (슈퍼포지션)

### 🤔 "치환"이란 무엇인가?

**치환**(substitution/rewriting)은 수학에서 가장 기본적인 추론이다:

> "A = B"라는 사실이 있으면, 어떤 식에서 A가 나올 때마다 B로 **바꿔 쓸 수 있다.**

이것은 일상에서도 흔히 하는 일이다:

```
"서울의 수도 = 대한민국의 수도"라는 사실을 알고 있으면,
"서울의 수도에 사는 사람"이라는 문장에서
"서울의 수도"를 "대한민국의 수도"로 바꿔 쓸 수 있다.
```

수학에서의 예:

```
가설: a = 5
목표: a + 3 = 8

치환(a를 5로 바꿈) 후:
목표: 5 + 3 = 8  ← 이제 계산으로 증명 가능!
```

### 💡 왜 "슈퍼포지션"이라고도 하나?

**슈퍼포지션**(superposition)은 자동 정리 증명(automated theorem proving) 분야에서
사용하는 용어이다. "등식에 의한 치환"이라는 뜻으로, `rw`가 하는 일과 본질적으로 같다.

- **치환**(substitution): 변수에 값을 대입하는 것 (예: `x := 5`)
- **대입**(rewriting): 등식을 이용해 한쪽을 다른 쪽으로 바꾸는 것 (예: `a = 5`이므로 `a`를 `5`로)
- **슈퍼포지션**(superposition): 위 과정을 체계적으로 자동화한 것

Lean 4의 `rw` 전술은 이 세 가지를 모두 수행한다.

### 🖥️ `rw` 전술 완전 해부

```lean
-- 가설(hypothesis)이 하나 있는 상황
example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  rw [h]
  -- 치환 전: ⊢ a + 1 = b + 1
  -- 치환 후: ⊢ b + 1 = b + 1  ← 자동으로 증명 완료!
```

`rw [h]`가 하는 일을 단계별로 보면:

1. `h : a = b`를 읽는다 → "a를 b로 바꿔라"
2. 목표에서 `a`를 찾는다
3. `a`를 `b`로 치환한다
4. 치환 후 목표가 `b + 1 = b + 1`이 되면 → **자동으로 증명 완료** (반사성, `rfl`)

### 🔄 역방향 치환: `rw [← h]`

`←`(왼쪽 화살표)를 붙이면 **반대 방향**으로 치환한다:

```lean
-- h : a = b 가 있을 때
-- rw [h]   는 목표에서 a → b 로 바꿈 (정방향)
-- rw [← h] 는 목표에서 b → a 로 바꿈 (역방향)

example (a b : Nat) (h : a = b) : b + 1 = a + 1 := by
  rw [← h]
  -- 치환 전: ⊢ b + 1 = a + 1
  -- 치환 후: ⊢ a + 1 = a + 1  ← 자동 완료!
```

`← h`는 `h`의 등식을 **오른쪽→왼쪽** 방향으로 사용한다.
VS Code에서 `←`는 `\l` 또는 `\leftarrow`로 입력한다.

### 📐 라이브러리 정리를 이용한 치환

Lean의 수학 라이브러리(Mathlib)에는 수많은 등식 정리가 있다.
이것들도 `rw`로 사용할 수 있다:

```lean
-- Mathlib의 등식 정리들
#check Nat.add_comm    -- ∀ (n m : Nat), n + m = m + n
#check Nat.add_assoc   -- ∀ (n m k : Nat), n + m + k = n + (m + k)
#check Nat.mul_comm    -- ∀ (n m : Nat), n * m = m * n
#check Nat.add_zero    -- ∀ (n : Nat), n + 0 = n
#check Nat.zero_add    -- ∀ (n : Nat), 0 + n = n

-- 사용 예
example (a b : Nat) : a + b = b + a := by
  rw [Nat.add_comm]
  -- 치환 후: ⊢ b + a = b + a  ← 자동 완료!

example (a : Nat) : a + 0 + 0 = a := by
  rw [Nat.add_zero]   -- a + 0 + 0 → a + 0
  rw [Nat.add_zero]   -- a + 0 → a
```

### 🔗 여러 치환을 한 번에

```lean
-- 쉼표로 구분하여 여러 치환을 한 줄에 쓸 수 있다
example (a : Nat) : a + 0 + 0 = a := by
  rw [Nat.add_zero, Nat.add_zero]

-- 인수를 줄 수도 있다
example (a b c : Nat) : a + b + c = a + (b + c) := by
  rw [Nat.add_assoc]
```

### ⚡ 가설에서의 치환: `rw [...] at h`

`rw`는 기본적으로 **목표**(goal)를 바꾸지만,
`at` 키워드를 쓰면 **가설**(hypothesis)도 바꿀 수 있다:

```lean
example (a b c : Nat) (h : a = b) (h2 : a + c = 10) : b + c = 10 := by
  rw [h] at h2
  -- h2가 "a + c = 10"에서 "b + c = 10"으로 변환됨
  exact h2
```

### ✏️ 연습 9I.3-a: 기본 치환 (괄호 채우기)

```lean
example (x y : Nat) (h : x = y) : x + x = y + y := by
  rw [/-[ 여기를 채우세요 ]-/]
```

<details>
<summary>✅ 답 보기</summary>

```lean
example (x y : Nat) (h : x = y) : x + x = y + y := by
  rw [h]
  -- x를 모두 y로 바꾸면 y + y = y + y → 자동 완료
```

</details>

### ✏️ 연습 9I.3-b: 역방향 치환 (괄호 채우기)

```lean
example (a b : Nat) (h : a = b) : b + 5 = a + 5 := by
  rw [/-[ 여기를 채우세요 ]-/]
```

<details>
<summary>✅ 답 보기</summary>

```lean
example (a b : Nat) (h : a = b) : b + 5 = a + 5 := by
  rw [← h]
  -- b를 a로 바꾸면 a + 5 = a + 5 → 자동 완료
```

</details>

### ✏️ 연습 9I.3-c: 라이브러리 정리로 치환 (sorry)

```lean
-- a + (b + 0) = b + a 를 증명하라
example (a b : Nat) : a + (b + 0) = b + a := by
  sorry
```

<details>
<summary>💡 힌트</summary>

1. 먼저 `b + 0`을 `b`로 바꾸자 → `rw [Nat.add_zero]`
2. 그 다음 `a + b`를 `b + a`로 바꾸자 → `rw [Nat.add_comm]`

</details>

<details>
<summary>✅ 답 보기</summary>

```lean
example (a b : Nat) : a + (b + 0) = b + a := by
  rw [Nat.add_zero]   -- a + (b + 0) → a + b
  rw [Nat.add_comm]   -- a + b → b + a
```

</details>

### ✏️ 연습 9I.3-d: 가설에서 치환 (sorry)

```lean
-- 가설 h2를 수정하여 목표를 증명하라
example (a b : Nat) (h : a = b + 1) (h2 : a + 3 = 10) : b + 1 + 3 = 10 := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
example (a b : Nat) (h : a = b + 1) (h2 : a + 3 = 10) : b + 1 + 3 = 10 := by
  rw [h] at h2    -- h2: a + 3 = 10 → b + 1 + 3 = 10
  exact h2
```

`rw [h] at h2`는 가설 `h2` 안에서 `a`를 `b + 1`로 치환한다.

</details>

---

## 9I.4 함의(→) — "만약 ~이면 ~이다"

### 🤔 일상에서의 "만약 ~이면"

> "만약 비가 오면, 우산을 가져간다."

이 문장은 **두 명제 사이의 관계**를 말한다:
- P = "비가 온다" (조건/가정)
- Q = "우산을 가져간다" (결론)
- P → Q = "비가 오면 우산을 가져간다" (함의)

수학에서도 같다:
- P = "n이 짝수이다"
- Q = "n²이 짝수이다"
- P → Q = "n이 짝수이면 n²도 짝수이다"

### 🖥️ Lean 4에서의 함의(→)

```lean
-- "만약 n = 0 이면, n + 5 = 5 이다"
example (n : Nat) : n = 0 → n + 5 = 5 := by
  intro h       -- h : n = 0 (가정을 받아들인다)
  rw [h]        -- n을 0으로 치환 → 0 + 5 = 5
  norm_num      -- 계산으로 확인
```

여기서 핵심 전술이 두 가지이다:

#### `intro` — "가정을 받아들이기"

`P → Q`를 증명할 때, `intro h`는 **"P가 참이라고 가정하자"**라는 뜻이다.
그러면 `h : P`라는 가설이 생기고, 목표는 `Q`로 바뀐다.

```
증명 전:                      intro h 후:
─────────                     ─────────
⊢ n = 0 → n + 5 = 5          h : n = 0
                              ⊢ n + 5 = 5
```

이것은 수학에서 "~라고 가정하자"라고 쓰는 것과 **완전히 동일**하다.

#### `apply` — "이미 알려진 함의를 사용하기"

반대로, `P → Q`라는 사실이 있고 `Q`를 증명해야 할 때,
`apply (P → Q)`를 하면 목표가 `P`로 바뀐다.

```lean
-- h는 "a = 5 → a + 1 = 6"이라는 함의
-- 목표가 "a + 1 = 6"일 때, apply h를 하면 목표가 "a = 5"로 바뀐다
example (a : Nat) (h : a = 5 → a + 1 = 6) (h2 : a = 5) : a + 1 = 6 := by
  apply h     -- 목표: a + 1 = 6 → a = 5 (h의 조건 부분)
  exact h2    -- h2가 a = 5을 증명
```

### 🔗 함의의 연쇄 (삼단논법)

```lean
-- P → Q → R 은 "P이면 Q이고, Q이면 R이다"가 아니다!
-- "P이면 (Q이면 R이다)"라는 뜻이다.
-- 즉 P와 Q를 모두 가정하면 R을 결론짓는다.

example (P Q R : Prop) (hpq : P → Q) (hqr : Q → R) : P → R := by
  intro hp        -- hp : P
  apply hqr       -- 목표: R → Q
  apply hpq       -- 목표: Q → P
  exact hp        -- hp : P ✓
```

이것은 **삼단논법**(modus ponens의 연쇄)이다:
- P가 참이면 Q가 참이고 (hpq)
- Q가 참이면 R이 참이다 (hqr)
- 따라서 P가 참이면 R이 참이다

### ✏️ 연습 9I.4-a: 기본 함의 (괄호 채우기)

```lean
-- "n = 3이면, n * 2 = 6이다"
example (n : Nat) : n = 3 → n * 2 = 6 := by
  /-[ 여기를 채우세요: 가정을 받아들이고 치환하라 ]-/
```

<details>
<summary>✅ 답 보기</summary>

```lean
example (n : Nat) : n = 3 → n * 2 = 6 := by
  intro h      -- h : n = 3
  rw [h]       -- 3 * 2 = 6
  norm_num
```

</details>

### ✏️ 연습 9I.4-b: apply 사용 (sorry)

```lean
-- 삼단논법을 증명하라
example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) (hp : P) : R := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) (hp : P) : R := by
  apply h2       -- 목표: Q
  apply h1       -- 목표: P
  exact hp       -- ✓

-- 또는 한 줄로:
-- exact h2 (h1 hp)
```

`h1 hp`는 "h1(P → Q)에 hp(P의 증거)를 적용"하여 Q의 증거를 만들고,
`h2 (h1 hp)`는 "h2(Q → R)에 Q의 증거를 적용"하여 R의 증거를 만든다.

</details>

### ✏️ 연습 9I.4-c: 여러 가정이 있는 함의 (sorry)

```lean
-- "a > 0이고 b > 0이면, a + b > 0이다"
example (a b : Nat) : a > 0 → b > 0 → a + b > 0 := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
example (a b : Nat) : a > 0 → b > 0 → a + b > 0 := by
  intro ha hb     -- ha : a > 0, hb : b > 0
  omega           -- 자연수 부등식을 자동 해결
```

`omega`는 자연수와 정수의 선형 부등식을 자동으로 증명하는 전술이다.

</details>

---

## 9I.5 동치(↔) — "~일 때 그리고 그때에만"

### 🤔 → 와 ↔ 는 뭐가 다른가?

| 기호 | 이름 | 의미 | 비유 |
|------|------|------|------|
| `→` | **함의**(implication) | "P이면 Q" | **일방통행** 도로 |
| `↔` | **동치**(iff, if and only if) | "P이면 Q, 그리고 Q이면 P" | **양방향** 도로 |

```
함의 (→):     P ───→ Q        (P에서 Q로만 갈 수 있음)
동치 (↔):     P ←──→ Q        (P에서 Q로, Q에서 P로 모두 갈 수 있음)
```

일상의 예:
- **함의**: "비가 오면 땅이 젖는다" (→) — 땅이 젖었다고 반드시 비가 온 건 아님
- **동치**: "n이 짝수 ↔ n을 2로 나누면 나머지가 0" — 양쪽 다 성립

### 🖥️ Lean 4에서의 ↔

`P ↔ Q`는 내부적으로 **(P → Q) ∧ (Q → P)**와 같다.
즉, **두 개의 함의가 합쳐진 것**이다!

```lean
-- ↔ 를 증명하려면: 두 방향을 각각 보여야 한다
example (n : Nat) : n = 0 ↔ n + 1 = 1 := by
  constructor           -- 두 방향으로 나눔
  · -- (→ 방향) n = 0 → n + 1 = 1
    intro h
    rw [h]
  · -- (← 방향) n + 1 = 1 → n = 0
    intro h
    omega
```

#### `constructor` — 동치를 두 방향으로 나누기

`P ↔ Q`가 목표일 때 `constructor`를 쓰면:
- 첫 번째 목표: `P → Q` (정방향)
- 두 번째 목표: `Q → P` (역방향)

### 🔧 ↔ 에서 한쪽 방향만 꺼내기

이미 증명된 `h : P ↔ Q`가 있을 때:

| 표현 | 의미 | 결과 |
|------|------|------|
| `h.mp` | 정방향 (modus ponens) | `P → Q` |
| `h.mpr` | 역방향 (modus ponens reverse) | `Q → P` |
| `h.1` | `h.mp`의 별명 | `P → Q` |
| `h.2` | `h.mpr`의 별명 | `Q → P` |

```lean
-- 사용 예
example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  exact h.mp hp    -- 또는 exact h.1 hp

example (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := by
  exact h.mpr hq   -- 또는 exact h.2 hq
```

### 🔄 ↔ 로 rw 하기

↔ 의 강력한 점: **`rw`에도 사용할 수 있다!**

```lean
-- 등식(=)뿐 아니라 동치(↔)도 rw로 치환할 수 있다
#check Nat.lt_iff_add_one_le
  -- Nat.lt_iff_add_one_le : m < n ↔ m + 1 ≤ n

example (m n : Nat) (h : m + 1 ≤ n) : m < n := by
  rw [Nat.lt_iff_add_one_le]
  exact h
```

### ✏️ 연습 9I.5-a: 동치 증명 (괄호 채우기)

```lean
-- "n + 0 = n ↔ 0 + n = n" 을 증명하라
example (n : Nat) : n + 0 = n ↔ 0 + n = n := by
  /-[ 여기를 채우세요: constructor로 나누고 각 방향을 증명하라 ]-/
```

<details>
<summary>✅ 답 보기</summary>

```lean
example (n : Nat) : n + 0 = n ↔ 0 + n = n := by
  constructor
  · intro _; omega
  · intro _; omega
```

양쪽 다 `omega`가 해결해주지만, 두 방향을 **각각** 보여야 한다는 점이 핵심이다.

</details>

### ✏️ 연습 9I.5-b: .mp와 .mpr 사용 (sorry)

```lean
-- h : P ↔ Q 를 이용하여 P ∧ Q를 증명하라 (P가 참일 때)
example (P Q : Prop) (h : P ↔ Q) (hp : P) : P ∧ Q := by
  sorry
```

<details>
<summary>💡 힌트</summary>

`And.intro`(또는 `⟨_, _⟩`)를 써서 P와 Q를 각각 증명한다.
Q는 `h.mp hp`로 얻을 수 있다.

</details>

<details>
<summary>✅ 답 보기</summary>

```lean
example (P Q : Prop) (h : P ↔ Q) (hp : P) : P ∧ Q := by
  exact ⟨hp, h.mp hp⟩
  -- 또는:
  -- constructor
  -- · exact hp
  -- · exact h.mp hp
```

</details>

### ✏️ 연습 9I.5-c: rw와 ↔ 결합 (sorry)

```lean
-- rw로 동치를 사용하여 증명하라
-- Nat.succ_le_iff : n + 1 ≤ m ↔ n < m 를 사용한다
example (n m : Nat) (h : n < m) : n + 1 ≤ m := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
example (n m : Nat) (h : n < m) : n + 1 ≤ m := by
  rw [Nat.succ_le_iff]   -- 목표가 n < m 으로 바뀜
  exact h

-- 또는: exact Nat.succ_le_iff.mpr h
```

`rw [Nat.succ_le_iff]`는 동치의 왼쪽(`n + 1 ≤ m`)을 오른쪽(`n < m`)으로 바꾼다.
이것은 `←`를 써서 `rw [← Nat.succ_le_iff]`로 반대 방향도 가능하다.

</details>

---

## 9I.6 → 와 ↔ 의 차이 — 한눈에 보기

이 섹션에서는 두 개념을 **표로** 정리하고, **같은 주제를 두 방식으로** 표현하는 연습을 한다.

### 📋 완전 비교표

| 속성 | 함의 `→` | 동치 `↔` |
|------|---------|---------|
| **읽는 법** | "P이면 Q" | "P일 때 그리고 그때에만 Q" |
| **방향** | 단방향 (P에서 Q로만) | 양방향 (P↔Q) |
| **증명 방법** | `intro h` | `constructor` (두 방향) |
| **사용 방법** | `apply h` 또는 `exact h hp` | `h.mp`, `h.mpr`, `rw [h]` |
| **분해** | 불가 (하나의 함수) | `h.1`(→), `h.2`(←) |
| **rw 가능?** | ❌ (등식/동치만 가능) | ✅ |
| **내부 구조** | 함수 `P → Q` | `(P → Q) ∧ (Q → P)` |
| **수학 표기** | ⇒ 또는 → | ⇔ 또는 ↔ |

### 💡 핵심 기억법

```
→ (함의) = 일방통행 표지판 🚗➡️
↔ (동치) = 양방향 통행 🚗↔️🚗
```

- `→`는 **조건이 참일 때 결론도 참**이라는 것만 보장한다.
  역방향은 보장하지 않는다.
- `↔`는 **양쪽 다 성립**한다.
  하나가 참이면 다른 하나도 참이고, 하나가 거짓이면 다른 하나도 거짓이다.

### ✏️ 연습 9I.6-a: → vs ↔ 구분 연습 (sorry)

```lean
-- (1) 이것은 → (일방통행)
-- "n이 0이면 n ≤ 5" — 참이지만 역방향은 안 됨 (n=3이면 n≤5이지만 n≠0)
example (n : Nat) : n = 0 → n ≤ 5 := by
  sorry

-- (2) 이것은 ↔ (양방향)
-- "n + 0 = n ↔ True" — 항상 참
example (n : Nat) : n + 0 = n ↔ True := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
-- (1) 함의
example (n : Nat) : n = 0 → n ≤ 5 := by
  intro h
  omega

-- (2) 동치
example (n : Nat) : n + 0 = n ↔ True := by
  constructor
  · intro _; trivial
  · intro _; omega
```

</details>

---

## 9I.7 `calc` — 계산풍 증명

### 🤔 수학 노트에서 하는 계산

중학교 수학에서 이런 풀이를 많이 본다:

```
  (a + b)² 
= a² + 2ab + b²      (전개)
= a² + 2·3 + b²      (ab = 3 대입)
= a² + 6 + b²        (계산)
```

각 줄에서 **한 단계씩** 변형하고, 왜 그런지 괄호 안에 적는다.
Lean 4의 `calc`는 이 방식을 **그대로** 코드로 옮긴 것이다!

### 🖥️ `calc` 기본 구조

```lean
example (a b c : Nat) (h1 : a = b + 1) (h2 : b = c + 2) : a = c + 3 := by
  calc a
    _ = b + 1     := by rw [h1]      -- ← 첫 번째 단계
    _ = (c + 2) + 1 := by rw [h2]    -- ← 두 번째 단계
    _ = c + 3     := by omega        -- ← 세 번째 단계
```

`calc`의 규칙:
1. 첫 줄에 시작 표현식을 쓴다 (여기서는 `a`)
2. 각 줄은 `_ = ...` 또는 `_ ≤ ...` 형태이다
3. `:= by ...`로 그 단계의 정당화를 쓴다
4. `_`는 "이전 줄의 오른쪽"을 의미한다

### 📐 부등식 calc

`calc`는 등식(`=`)뿐 아니라 부등식(`≤`, `<`)도 다룰 수 있다:

```lean
example (a b c : Nat) (h1 : a ≤ b) (h2 : b < c) : a < c := by
  calc a
    _ ≤ b := h1
    _ < c := h2
```

등식과 부등식을 **섞어서** 쓸 수도 있다!

### ✏️ 연습 9I.7-a: calc 증명 (괄호 채우기)

```lean
example (x y : Nat) (h : x = y + 2) : x + 3 = y + 5 := by
  calc x + 3
    _ = /-[ 여기를 채우세요 ]-/ := by rw [h]
    _ = y + 5 := by /-[ 여기를 채우세요 ]-/
```

<details>
<summary>✅ 답 보기</summary>

```lean
example (x y : Nat) (h : x = y + 2) : x + 3 = y + 5 := by
  calc x + 3
    _ = (y + 2) + 3 := by rw [h]
    _ = y + 5 := by omega
```

</details>

### ✏️ 연습 9I.7-b: 긴 calc 증명 (sorry)

```lean
-- a + b + c = c + b + a 를 calc로 증명하라
example (a b c : Nat) : a + b + c = c + b + a := by
  sorry
```

<details>
<summary>💡 힌트</summary>

`Nat.add_comm`과 `Nat.add_assoc`를 `rw`로 사용하거나,
각 단계에서 `omega`를 쓸 수도 있다.
가장 간단한 방법은 `omega` 한 줄이지만, `calc` 연습을 위해 여러 단계로 풀어보자.

</details>

<details>
<summary>✅ 답 보기</summary>

```lean
-- 방법 1: calc 사용
example (a b c : Nat) : a + b + c = c + b + a := by
  calc a + b + c
    _ = a + (b + c) := by rw [Nat.add_assoc]
    _ = a + (c + b) := by rw [Nat.add_comm b c]
    _ = (c + b) + a := by rw [Nat.add_comm a (c + b)]
    _ = c + b + a   := by rfl

-- 방법 2: omega (자동)
example (a b c : Nat) : a + b + c = c + b + a := by omega
```

</details>

---

## 9I.8 종합 연습 — 모든 것을 한꺼번에

지금까지 배운 것을 총동원하는 연습이다.

### ✏️ 연습 9I.8-a: lemma + rw + → 결합 (sorry)

```lean
-- 보조정리를 만들고, 이를 사용하여 정리를 증명하라
lemma double_eq (n : Nat) : n + n = 2 * n := by
  sorry

theorem sum_eq (a b : Nat) : a + a + (b + b) = 2 * a + 2 * b := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
lemma double_eq (n : Nat) : n + n = 2 * n := by
  omega

theorem sum_eq (a b : Nat) : a + a + (b + b) = 2 * a + 2 * b := by
  rw [double_eq a, double_eq b]
```

</details>

### ✏️ 연습 9I.8-b: ↔ + constructor + rw 결합 (sorry)

```lean
-- n * 2 = n + n ↔ True 를 증명하라
example (n : Nat) : n * 2 = n + n ↔ True := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
example (n : Nat) : n * 2 = n + n ↔ True := by
  constructor
  · intro _; trivial
  · intro _; omega
```

</details>

### ✏️ 연습 9I.8-c: apply + intro + rw 종합 (sorry)

```lean
-- "a = b이고 b = c이면, a + 1 = c + 1이다"
example (a b c : Nat) : a = b → b = c → a + 1 = c + 1 := by
  sorry
```

<details>
<summary>✅ 답 보기</summary>

```lean
example (a b c : Nat) : a = b → b = c → a + 1 = c + 1 := by
  intro hab hbc
  rw [hab, hbc]
  -- 또는: omega 대신 rw 두 번
```

</details>

### ✏️ 연습 9I.8-d: 이산수학 연결 — 곱셈 법칙 (sorry)

```lean
-- Rosen §6.1 곱셈 법칙:
-- "n가지 × m가지 = n*m가지"를 Fintype으로 표현
-- Fin n의 원소 수가 n개임을 보이기

open Fintype in
example (n m : Nat) : card (Fin n × Fin m) = n * m := by
  sorry
```

<details>
<summary>💡 힌트</summary>

`simp`가 해결해 준다. Lean은 `Fin n`의 원소 수가 `n`임을 알고 있다.

</details>

<details>
<summary>✅ 답 보기</summary>

```lean
open Fintype in
example (n m : Nat) : card (Fin n × Fin m) = n * m := by
  simp
```

이것이 Part 9-A에서 배운 곱셈 법칙의 Lean 4 형식화이다.
`Fin n × Fin m`은 "n가지 선택 × m가지 선택"을 타입으로 표현한 것이고,
`card`는 그 타입의 원소 수(경우의 수)를 센다.

</details>

---

## 📋 9I.9 이 파트에서 배운 전술 요약

| 전술 | 하는 일 | 예시 |
|------|---------|------|
| `rw [h]` | 등식/동치로 목표를 **치환** | `rw [Nat.add_comm]` |
| `rw [← h]` | **역방향** 치환 | `rw [← h]` |
| `rw [...] at h` | **가설에서** 치환 | `rw [h1] at h2` |
| `intro h` | 함의의 **가정을 받아들임** | `intro h` |
| `apply h` | 함의를 **역방향으로 적용** | `apply le_trans` |
| `exact h` | 가설이 **목표와 정확히 일치** | `exact h` |
| `constructor` | `∧` 또는 `↔`를 **두 부분으로 분리** | `constructor` |
| `calc` | **계산풍** 단계별 증명 | `calc a _ = b := ...` |
| `norm_num` | 구체적 **숫자 계산** | `norm_num` |
| `omega` | 자연수/정수 **선형 산술** | `omega` |
| `simp` | **간소화** 규칙 자동 적용 | `simp` |
| `trivial` | `True` 등 **자명한 것** 증명 | `trivial` |

---

## 🔗 다음 파트 미리보기

**Part 9-J**에서는 이번 파트에서 배운 기초 도구들(`rw`, `intro`, `apply`, `calc`, `↔`)을
사용하여, Rosen 이산수학 6.5절(일반화된 순열과 조합)의 문제들을 Lean 4로 **본격적으로** 풀어본다.
반복 허용 순열(nʳ), 중복 조합(별과 막대), 다항 계수, 객체 분배 등을 다룬다.
