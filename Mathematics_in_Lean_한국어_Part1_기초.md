# 『Mathematics in Lean』 한국어 튜토리얼 — Part 1: 기초 중의 기초

> **원서**: *Mathematics in Lean* (Jeremy Avigad, Patrick Massot) Release v4.19.0
> **대상**: Lean 4에서 **정리**(theorem)가 뭔지도 모르는 중학생
> **목표**: `rw`(치환/대입 = 슈퍼포지션), `lemma`와 `theorem`의 관계, `→`(if)와 `↔`(iff)의 차이를 한 번에 이해하기

---

## 0. Lean 4란 무엇인가?

### 0.1 한 줄 요약

> Lean 4는 **수학 증명을 컴퓨터가 검사해 주는 도구**이다.

우리가 수학 문제를 풀 때, 선생님이 답안지를 채점하듯이, Lean 4는 우리가 쓴 증명이 맞는지 틀렸는지 **즉시** 알려준다. 틀리면 빨간 줄이 뜨고, 맞으면 아무 에러도 안 뜬다. 정말 단순하다!

### 0.2 비유로 이해하기

일상생활의 비유를 들어보자.

| 일상 | Lean 4 |
|------|--------|
| 수학 문제를 푼다 | **증명**(proof)을 작성한다 |
| 선생님이 채점한다 | Lean이 **타입 검사**(type check)한다 |
| "이 공식을 써라" | **정리**(theorem)나 **작은 정리**(lemma)를 적용한다 |
| 식에서 값을 대입한다 | `rw`(**치환**)를 사용한다 |
| 정답입니다 ✓ | 에러 없음 (초록불) |
| 오답입니다 ✗ | 빨간 밑줄 + 에러 메시지 |

### 0.3 설치 없이 맛보기

Lean 4를 설치하지 않아도 아래 내용을 읽으며 "아, 이런 거구나" 하고 감을 잡을 수 있다. 나중에 직접 해보고 싶다면 [공식 설치 안내](https://leanprover-community.github.io/get_started.html)를 따르면 된다.

---

## 1. 모든 것에는 **타입**(Type)이 있다

### 1.1 타입이란?

Lean 4의 세계에서 **모든 것**은 **타입**(type)을 가진다. "이 물건은 어떤 종류인가?"라고 물을 때, 그 "종류"가 바로 타입이다.

현실 세계로 비유하면:

| 물건 | 종류(타입) |
|------|-----------|
| 3 | 자연수(`ℕ`) |
| -5 | 정수(`ℤ`) |
| 3.14 | 실수(`ℝ`) |
| "안녕" | 문자열(`String`) |
| `true` | 불리언(`Bool`) |

Lean 4에서는 `#check` 명령어로 어떤 것의 타입을 확인할 수 있다:

```lean
#check 2 + 2        -- 2 + 2 : ℕ   (자연수 타입)
#check (3.14 : ℝ)   -- 3.14 : ℝ   (실수 타입)
```

> 💡 **핵심**: `#check`는 "너 뭐야?"라고 묻는 명령어다. Lean은 "나는 ℕ(자연수)야"처럼 답한다.

### 1.2 함수에도 타입이 있다

함수(function)도 타입을 가진다. "자연수를 받아서 자연수를 돌려주는 함수"의 타입은 `ℕ → ℕ`이다.

```lean
def f (x : ℕ) := x + 3    -- f는 자연수를 받아 3을 더하는 함수

#check f      -- f : ℕ → ℕ
#check f 5    -- f 5 : ℕ   (결과값은 8, 자연수)
```

여기서 화살표 `→`가 처음 등장하는데, 지금은 "~를 받아서 ~를 돌려준다"라는 뜻으로만 이해하면 된다. (나중에 논리적 의미도 배운다!)

### 1.3 수학적 명제(Prop)도 타입이다 — 이것이 핵심!

여기서 Lean 4의 정말 놀라운 점이 나온다.

> **수학적 명제(statement)도 타입이다.**

```lean
#check 2 + 2 = 4    -- 2 + 2 = 4 : Prop
```

`2 + 2 = 4`는 `Prop`이라는 타입을 가진다. `Prop`은 **명제**(Proposition)의 줄임말로, "참이거나 거짓인 수학적 진술"을 뜻한다.

그럼 이 명제의 **증명**은 뭘까?

> **어떤 명제 `P`의 증명은, 타입이 `P`인 "값"이다.**

이게 무슨 말인지 비유로 설명하겠다:

| 개념 | 비유 |
|------|------|
| 명제 `2 + 2 = 4` | "빈 상자"에 `2 + 2 = 4`라는 라벨이 붙어있다 |
| 이 명제의 증명 | 그 상자 안에 넣을 수 있는 **증거물** |
| 증명이 완성되면 | 상자 안에 증거물이 들어가서 Lean이 "OK!" 한다 |

```lean
-- "2 + 2 = 4"의 증명을 만들어보자
theorem easy : 2 + 2 = 4 := rfl

#check easy    -- easy : 2 + 2 = 4
```

`rfl`은 "**반사성**(reflexivity)"의 줄임말로, "양쪽이 **정의상** 같다"는 뜻이다. `2 + 2`를 계산하면 `4`이고, `4 = 4`이니까 당연히 같다!

### 1.4 `sorry` — "아직 증명 못했어요" 표시

증명을 아직 완성하지 못했을 때 `sorry`를 쓸 수 있다. 마치 시험에서 "풀이 생략"이라고 쓰는 것과 같다.

```lean
theorem hard : ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n := sorry
```

위는 유명한 **페르마의 마지막 정리**(Fermat's Last Theorem)이다. `sorry`로 일단 넘어갈 수 있지만, Lean은 이것이 "미완성"이라는 것을 알고 있다. 경고를 표시한다.

> ⚠️ `sorry`는 연습할 때 유용하지만, **최종 증명에서는 절대 남겨두면 안 된다**. 마치 시험에서 "풀이 생략"으로는 점수를 받을 수 없는 것과 같다.

---

## 2. **정리**(theorem)와 **작은 정리**(lemma): 사실 똑같다!

### 2.1 `theorem`과 `lemma`의 정의

수학 교과서에서는 보통 이렇게 구분한다:

| 용어 | 의미 | 비유 |
|------|------|------|
| **정리**(theorem) | 중요하고 큰 결과 | 건물 전체 |
| **보조정리**(lemma) | 큰 정리를 증명하기 위한 작은 결과 | 건물의 벽돌 하나 |

예를 들어:
- **피타고라스 정리**(Pythagorean Theorem)는 **정리**이다 — 그 자체로 유명하고 중요하다.
- "직각삼각형에서 높이를 내리면 두 개의 작은 직각삼각형이 생긴다"는 **보조정리**이다 — 피타고라스 정리를 증명하는 데 쓰이는 중간 단계이다.

### 2.2 Lean 4에서는 — 완전히 동일하다!

**놀라운 사실**: Lean 4에서 `theorem`과 `lemma`는 기능적으로 **완전히 동일**하다. 어떤 것을 써도 Lean은 전혀 구분하지 않는다.

```lean
-- 이 두 개는 Lean 입장에서 완전히 같다!
theorem my_theorem : 2 + 3 = 5 := rfl
lemma my_lemma : 2 + 3 = 5 := rfl

-- 둘 다 똑같이 사용할 수 있다
#check my_theorem   -- my_theorem : 2 + 3 = 5
#check my_lemma     -- my_lemma : 2 + 3 = 5
```

그렇다면 왜 두 가지 이름이 있는 걸까?

### 2.3 이름이 다른 이유: 인간을 위한 분류

`theorem`과 `lemma`의 구분은 **인간 독자**를 위한 것이다:

- `theorem`이라고 이름 붙이면: "이것은 중요한 최종 결과입니다"라는 신호
- `lemma`라고 이름 붙이면: "이것은 보조 도구입니다. 다른 증명에서 쓰일 겁니다"라는 신호

Lean의 수학 라이브러리 **Mathlib**에서도 이 관례를 따른다. 하지만 기억하자:

> 📌 **기억하기**: Lean 4에서 `theorem`과 `lemma`는 **완전히 같은 기능**이다. 단지 읽는 사람에게 주는 힌트가 다를 뿐이다.

### 2.4 `example` — 이름 없는 연습 문제

`theorem`이나 `lemma`와 비슷하지만, **이름이 없는** 것이 `example`이다:

```lean
example : 2 + 3 = 5 := rfl
```

`example`은 "이런 게 가능하다"를 보여주는 데 쓰인다. 이름이 없으므로 나중에 다시 불러서 쓸 수 없다. 연습 문제에 딱 좋다!

| 키워드 | 이름 있음? | 나중에 재사용? | 용도 |
|--------|-----------|---------------|------|
| `theorem` | ✅ | ✅ | 중요한 최종 결과 |
| `lemma` | ✅ | ✅ | 보조 도구, 중간 단계 |
| `example` | ❌ | ❌ | 연습, 데모, 예시 |

---

## 3. `rw` — **치환**(대입) = **슈퍼포지션**(Superposition)

### 3.1 `rw`란 무엇인가?

`rw`는 **rewrite**(다시 쓰기)의 줄임말이다. 수학에서 "등식의 한쪽을 다른 쪽으로 바꿔치기"하는 것이다.

이것을 **치환**(substitution) 또는 **대입**이라고 부르며, 논리학에서는 **슈퍼포지션**(superposition)이라고도 한다.

> **슈퍼포지션**의 원래 뜻: "같다고 알려진 것을 겹쳐놓기(superpose)"
>
> `A = B`라는 사실이 있을 때, 어떤 식에서 `A`가 보이면 `B`로 바꿔놓을 수 있다.

### 3.2 가장 간단한 예제

중학교 수학을 떠올려보자. `x = 3`이면 `x + 2`는 `3 + 2 = 5`가 된다. 이것이 바로 치환이다!

Lean 4에서도 똑같다:

```lean
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]      -- a * b를 b * a로 바꾼다
  rw [mul_assoc b a c]   -- b * a * c를 b * (a * c)로 바꾼다
```

한 줄씩 따라가보자:

**시작 상태** (증명해야 할 것):
```
⊢ a * b * c = b * (a * c)
```

**1단계**: `rw [mul_comm a b]`
- `mul_comm a b`는 "`a * b = b * a`"라는 사실이다 (곱셈의 **교환법칙**)
- 이 사실을 이용해서, 목표에 있는 `a * b`를 `b * a`로 **치환**한다
- 결과:
```
⊢ b * a * c = b * (a * c)
```

**2단계**: `rw [mul_assoc b a c]`
- `mul_assoc b a c`는 "`b * a * c = b * (a * c)`"라는 사실이다 (곱셈의 **결합법칙**)
- 목표에 있는 `b * a * c`를 `b * (a * c)`로 **치환**한다
- 결과:
```
⊢ b * (a * c) = b * (a * c)
```

양쪽이 같으므로, Lean이 자동으로 "증명 완료!"라고 한다. 🎉

### 3.3 `rw`의 방향: 왼쪽 → 오른쪽, 오른쪽 → 왼쪽

`rw`는 기본적으로 **등식의 왼쪽을 오른쪽으로** 바꾼다.

```
mul_comm a b : a * b = b * a
               ─────   ─────
               왼쪽     오른쪽

rw [mul_comm a b]  →  목표에서 "a * b"를 찾아 "b * a"로 바꿈
```

반대 방향으로 바꾸고 싶으면? 화살표 `←`를 붙인다:

```lean
rw [← mul_comm a b]   -- 목표에서 "b * a"를 찾아 "a * b"로 바꿈
```

> 💡 `←`는 VS Code에서 `\l` 또는 `\leftarrow`로 입력한다.

비유하면:
- `rw [h]` = 등식 `h`를 **정방향**으로 적용 (왼쪽 → 오른쪽)
- `rw [← h]` = 등식 `h`를 **역방향**으로 적용 (오른쪽 → 왼쪽)

### 3.4 여러 번 치환하기 — 한 줄에 쭉!

`rw`를 여러 번 쓰는 대신, 대괄호 안에 콤마로 나열할 수 있다:

```lean
-- 긴 버전 (한 줄씩)
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- 짧은 버전 (한 줄에)
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b, mul_assoc b a c]
```

둘은 완전히 같은 증명이다. 마치 계산을 한 줄에 쭉 쓰는 것과 같다.

### 3.5 `rw`가 쓰는 재료: `#check`로 확인하기

`rw`에 넣을 수 있는 "재료"는 무엇인가? **등식**(=) 또는 **동치**(↔) 형태의 정리이다.

```lean
-- 이런 정리들을 rw에 넣을 수 있다
#check (mul_comm : ∀ a b : ℝ, a * b = b * a)
#check (mul_assoc : ∀ a b c : ℝ, a * b * c = a * (b * c))
#check (add_comm : ∀ a b : ℝ, a + b = b + a)
#check (two_mul : ∀ a : ℝ, 2 * a = a + a)
```

> 💡 **핵심**: `rw [X]`에서 `X`는 반드시 `A = B` 또는 `A ↔ B` 형태여야 한다. `rw`는 "같은 것끼리 바꿔치기"를 하는 전문가이다.

### 3.6 가설(hypothesis)에서 치환하기: `rw [...] at h`

지금까지는 **목표**(goal, 증명해야 할 것)에서 치환했다. 하지만 **가설**(hypothesis, 이미 알고 있는 사실)에서도 치환할 수 있다.

```lean
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp     -- hyp에서 b를 a * d로 바꿈
                        -- hyp가 c = d * a + a * d가 됨
  rw [mul_comm d a] at hyp  -- hyp에서 d * a를 a * d로 바꿈
                        -- hyp가 c = a * d + a * d가 됨
  rw [← two_mul (a * d)] at hyp  -- hyp에서 a*d + a*d를 2*(a*d)로 바꿈
  rw [← mul_assoc 2 a d] at hyp  -- hyp에서 2*(a*d)를 2*a*d로 바꿈
  exact hyp             -- hyp와 목표가 정확히 일치! 증명 끝!
```

- `rw [...] at hyp` = "가설 `hyp`에서 치환해라"
- `exact hyp` = "`hyp`가 목표와 정확히 같으니, 이것으로 증명 끝!"

### 3.7 정리: `rw` 치환 요약표

| 표현 | 의미 | 비유 |
|------|------|------|
| `rw [h]` | 목표에서 `h`의 왼쪽을 오른쪽으로 바꿈 | 정방향 대입 |
| `rw [← h]` | 목표에서 `h`의 오른쪽을 왼쪽으로 바꿈 | 역방향 대입 |
| `rw [h] at hyp` | 가설 `hyp`에서 치환 | 이미 아는 사실을 변형 |
| `rw [h1, h2, h3]` | 연속으로 세 번 치환 | 계산을 쭉 이어서 |

---

## 4. `→`(**함의**, if)와 `↔`(**동치**, iff)의 차이

### 4.1 일상 비유부터 시작하자

| 기호 | 읽는 법 | 뜻 | 일상 비유 |
|------|---------|-----|----------|
| `→` | "이면" (if ... then) | **한 방향** | 비가 오면 → 땅이 젖는다 |
| `↔` | "일 때 그리고 그때만" (iff) | **양 방향** | 삼각형이 정삼각형 ↔ 세 변의 길이가 같다 |

#### `→`(함의, Implication): 한 방향 화살표

"A → B"는 "A이면 B이다"를 뜻한다.

예: "비가 오면 땅이 젖는다"
- 비가 올 때(A가 참) → 땅이 젖는다(B가 참) ✓
- 비가 안 오면? → B에 대해 아무 말도 할 수 없다 (스프링클러 때문에 젖을 수도!)

> **핵심**: `A → B`에서 A가 참이면 B도 참이지만, B가 참이라고 A가 참인 건 아니다.

#### `↔`(동치, Biconditional): 양 방향 화살표

"A ↔ B"는 "A이면 B이고, B이면 A이다"를 뜻한다. 즉 `(A → B) ∧ (B → A)`이다.

예: "정삼각형이다 ↔ 세 변의 길이가 같다"
- 정삼각형이면 → 세 변의 길이가 같다 ✓
- 세 변의 길이가 같으면 → 정삼각형이다 ✓
- **양쪽 다 성립!**

### 4.2 Lean 4에서의 `→`

Lean 4에서 `→`는 두 가지 역할을 한다:

1. **함수의 타입**: `ℕ → ℕ`은 "자연수를 받아 자연수를 돌려주는 함수"
2. **논리적 함의**: `P → Q`는 "P이면 Q이다"

사실 이 둘은 Lean 내부적으로 **같은 것**이다! "P의 증명을 받아서 Q의 증명을 돌려주는 함수"가 바로 "P이면 Q이다"의 증명이기 때문이다. (이것을 **커리-하워드 대응**(Curry-Howard correspondence)이라 한다. 지금은 이름만 알아두자.)

```lean
-- "0 ≤ x이면 |x| = x이다"
#check ∀ x : ℝ, 0 ≤ x → |x| = x
```

#### `→`의 증명: `intro`

"P → Q"를 증명하려면:
1. "P가 참이라고 가정하자" (`intro h` — 가정 `h`를 도입)
2. 그 가정 아래서 Q를 증명한다

```lean
-- "a ≤ b이면, a + c ≤ b + c이다"
example (a b c : ℝ) : a ≤ b → a + c ≤ b + c := by
  intro h          -- h : a ≤ b 라고 가정
  linarith         -- 나머지는 산술 자동 증명기가 해결!
```

#### `→`의 사용: `apply` 또는 직접 적용

이미 증명된 `h : P → Q`가 있고, `hp : P`(P의 증명)가 있으면:
- `h hp`로 `Q`의 증명을 얻는다 (함수 적용처럼!)

```lean
-- my_lemma : ... → ... → ... → |x * y| < ε
-- 이 정리를 "적용"하면, 각 전제조건이 새로운 목표가 된다
-- apply my_lemma
```

### 4.3 Lean 4에서의 `↔`

`↔`는 **양방향 함의**이다. `A ↔ B`는 `(A → B) ∧ (B → A)`와 같다.

```lean
-- "exp a ≤ exp b ↔ a ≤ b" 라는 정리가 있다
#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
```

#### `↔`를 분해하기: `.mp`와 `.mpr`

`↔`는 두 개의 `→`로 이루어져 있으므로, 각각을 꺼낼 수 있다:

| 표현 | 의미 | 방향 | 이름의 유래 |
|------|------|------|------------|
| `h.mp` | `A → B` | **정방향** | **m**odus **p**onens (긍정 논법) |
| `h.mpr` | `B → A` | **역방향** | **m**odus **p**onens **r**everse |
| `h.1` | `A → B` | 정방향 (`.mp`와 같음) | 첫 번째 |
| `h.2` | `B → A` | 역방향 (`.mpr`와 같음) | 두 번째 |

```lean
-- h : exp a ≤ exp b ↔ a ≤ b 일 때

-- 정방향: a ≤ b이면 exp a ≤ exp b
-- h.mpr : a ≤ b → exp a ≤ exp b

-- 역방향: exp a ≤ exp b이면 a ≤ b
-- h.mp : exp a ≤ exp b → a ≤ b
```

#### 실제 예제

```lean
example (h : a ≤ b) : exp a ≤ exp b := by
  rw [exp_le_exp]    -- ↔ 정리를 rw로! 목표가 a ≤ b로 바뀜
  exact h            -- h가 정확히 a ≤ b이므로 끝!
```

**여기서 핵심**: `rw`는 `=`(등호)뿐 아니라 `↔`(동치)에도 쓸 수 있다!

- `rw [등호 정리]` = 목표에서 한쪽을 다른 쪽으로 **바꿈**
- `rw [↔ 정리]` = 목표를 **동치인 다른 명제로 바꿈**

이것이 바로 `rw`의 강력함이다. 등호든 동치든, "같은 것끼리 바꿔치기"를 해준다!

### 4.4 `→`와 `↔` 비교 정리

| 특성 | `→` (함의) | `↔` (동치) |
|------|-----------|-----------|
| 읽는 법 | "이면" (if...then) | "일 때 그리고 그때만" (iff) |
| 방향 | **한 방향** | **양 방향** |
| 분해 | 분해 불가 (그 자체가 한 방향) | `.mp`(정방향) + `.mpr`(역방향) |
| `rw`에 쓸 수 있나? | ❌ (`=`이 아니므로) | ✅ (동치이므로 바꿔치기 가능) |
| 증명 방법 | `intro`로 전제 도입 | `constructor`로 두 방향 각각 증명 |
| 사용 방법 | `apply` 또는 직접 적용 | `.mp`, `.mpr`, 또는 `rw` |

### 4.5 `↔`의 증명: `constructor`

`A ↔ B`를 증명하려면 두 방향을 각각 증명해야 한다:

```lean
example (a b : ℝ) (h : a ≤ b) : ¬(b ≤ a) ↔ a ≠ b := by
  constructor           -- 두 개의 목표로 분리
  · -- 정방향: ¬(b ≤ a) → a ≠ b
    intro h₁ h₂       -- h₁ : ¬(b ≤ a), h₂ : a = b 라고 가정
    apply h₁           -- ¬(b ≤ a)에 모순을 일으키자
    rw [h₂]            -- a = b로 치환하면 b ≤ b를 증명하면 됨
  · -- 역방향: a ≠ b → ¬(b ≤ a)
    intro h₁ h₂       -- h₁ : a ≠ b, h₂ : b ≤ a 라고 가정
    apply h₁           -- a ≠ b에 모순을 일으키자
    exact le_antisymm h h₂  -- a ≤ b이고 b ≤ a이면 a = b
```

> 💡 가운뎃점 `·`은 "이 목표에 집중합니다"를 뜻한다. 목표가 여러 개일 때 각각 구분해서 증명하는 데 쓴다.

---

## 5. 계산하기: `calc` — 단계별 풀이

### 5.1 `calc`란?

시험에서 풀이를 단계별로 쓰듯이, Lean에서도 `calc`(calculation)으로 단계별 계산을 할 수 있다.

```lean
example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  calc
    (a + b) * (a + b)
        = a * a + b * a + (a * b + b * b) := by rw [mul_add, add_mul, add_mul]
      _ = a * a + (b * a + a * b) + b * b := by rw [← add_assoc, add_assoc (a * a)]
      _ = a * a + 2 * (a * b) + b * b     := by rw [mul_comm b a, ← two_mul]
```

각 줄의 `_`는 "바로 윗줄의 결과"를 의미한다. 마치:

```
(a + b)(a + b)
= a² + ba + ab + b²      ← 분배법칙
= a² + (ba + ab) + b²    ← 결합법칙
= a² + 2ab + b²          ← ba = ab이므로, ba + ab = 2ab
```

이것을 그대로 Lean으로 옮긴 것이다!

### 5.2 `ring` — 산술은 자동으로!

사실 위의 증명은 `ring` 한 줄로 끝낼 수 있다:

```lean
example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring
```

`ring`은 **환**(ring)의 공리만으로 증명 가능한 등식이면 자동으로 해결해 주는 마법 같은 **전술**(tactic)이다. 정말 편리하다!

하지만 `ring`이 모든 것을 해결해 주지는 않는다. 부등식이나 가설을 활용해야 하는 증명에서는 `rw`를 직접 써야 한다. 그래서 `rw`를 제대로 이해하는 것이 중요하다.

---

## 6. 연습문제

### 연습 1: `rw` 기초 (괄호 채우기)

> 아래 코드에서 `{?}`를 알맞은 것으로 채워라.

```lean
-- 곱셈의 교환법칙과 결합법칙을 써서 증명하기
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [{?} a b]          -- 힌트: a * b = b * a 를 만드는 정리
  rw [{?} b a c]        -- 힌트: b * a * c = b * (a * c) 를 만드는 정리
```

<details>
<summary>✅ 답 보기</summary>

```lean
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm a b]       -- 아, 잠깐! 실은 c * b를 먼저 다뤄야 한다
  -- 사실 이 문제는 좀 더 생각이 필요하다. 다시 해보자:

-- 올바른 풀이:
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]       -- c * b → b * c  (목표: b * c * a = b * (a * c))
  rw [mul_assoc b c a]    -- b * c * a → b * (c * a)  (목표: b * (c * a) = b * (a * c))
  rw [mul_comm c a]       -- c * a → a * c  (목표: b * (a * c) = b * (a * c))
```

**풀이 설명**:
1. 먼저 `c * b`를 `b * c`로 바꾸었다 (교환법칙)
2. 그다음 `b * c * a`를 `b * (c * a)`로 바꾸었다 (결합법칙)
3. 마지막으로 `c * a`를 `a * c`로 바꾸었다 (교환법칙)
4. 양쪽이 `b * (a * c)`로 같아져서 증명 완료!

</details>

### 연습 2: `rw` 기초 (괄호 채우기 — `ring` 없이)

```lean
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  rw [{?}]       -- 힌트: a ^ 2 = a * a 를 만드는 정리 이름은 pow_two
  sorry           -- 나머지는 직접 해보자!
```

<details>
<summary>✅ 답 보기</summary>

```lean
-- ring을 쓰면 한 줄:
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring
```

`ring`이 자동으로 해결해 준다. `rw`만으로 하려면 꽤 길어지는데, 이 단계에서는 `ring`을 쓰는 것이 현명하다!

</details>

### 연습 3: `→`의 이해 (sorry 채우기)

```lean
-- "a ≤ b이고 c < d이면, a + c < b + d이다"
example (a b c d : ℝ) (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d := by
  sorry
  -- 힌트: add_lt_add_of_le_of_lt라는 정리가 있다
  -- #check add_lt_add_of_le_of_lt
```

<details>
<summary>✅ 답 보기</summary>

```lean
example (a b c d : ℝ) (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d := by
  exact add_lt_add_of_le_of_lt h₁ h₂
  -- 또는
  -- linarith
```

`add_lt_add_of_le_of_lt`는 "a ≤ b이고 c < d이면 a + c < b + d"라는 정리이다. `h₁`(a ≤ b의 증거)과 `h₂`(c < d의 증거)를 넣으면 목표가 바로 증명된다.

`linarith`는 **선형 산술**(linear arithmetic)을 자동으로 처리해 주는 전술로, 이런 종류의 부등식을 한 방에 해결한다.

</details>

### 연습 4: `↔`의 이해 (sorry 채우기)

```lean
-- exp_le_exp : exp a ≤ exp b ↔ a ≤ b 를 이용
example (a b : ℝ) (h : a ≤ b) : exp a ≤ exp b := by
  sorry
  -- 힌트 1: rw [exp_le_exp] 를 쓰거나
  -- 힌트 2: exact exp_le_exp.mpr h 를 쓰거나
```

<details>
<summary>✅ 답 보기</summary>

```lean
-- 방법 1: rw로 목표를 동치인 것으로 바꿈
example (a b : ℝ) (h : a ≤ b) : exp a ≤ exp b := by
  rw [exp_le_exp]
  exact h

-- 방법 2: .mpr로 역방향 직접 적용
example (a b : ℝ) (h : a ≤ b) : exp a ≤ exp b := by
  exact exp_le_exp.mpr h

-- 방법 3: 한 줄 증명항
example (a b : ℝ) (h : a ≤ b) : exp a ≤ exp b :=
  exp_le_exp.mpr h
```

**방법 1 설명**: `rw [exp_le_exp]`는 목표 `exp a ≤ exp b`를 동치인 `a ≤ b`로 바꾼다. 그러면 `h`가 정확히 `a ≤ b`이므로 `exact h`로 끝!

**방법 2 설명**: `exp_le_exp`는 `↔`이므로 `.mpr`(역방향: `a ≤ b → exp a ≤ exp b`)을 꺼내고, `h`를 넣으면 바로 증명!

</details>

### 연습 5: `rw at` (가설에서 치환 — sorry 채우기)

```lean
example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  sorry
  -- 힌트: hyp'를 hyp에 대입하면, c = b * a - a * b가 되고,
  --       b * a = a * b이므로, c = a * b - a * b = 0
  -- 쓸 수 있는 도구: rw, mul_comm, sub_self
```

<details>
<summary>✅ 답 보기</summary>

```lean
example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp'] at hyp        -- hyp: c = b * a - a * b
  rw [mul_comm b a] at hyp  -- hyp: c = a * b - a * b
  rw [sub_self] at hyp     -- hyp: c = 0
  exact hyp                 -- 목표와 정확히 일치!
```

**단계별 설명**:
1. `rw [hyp'] at hyp`: `hyp`에서 `d`를 `a * b`로 치환 → `hyp : c = b * a - a * b`
2. `rw [mul_comm b a] at hyp`: `hyp`에서 `b * a`를 `a * b`로 치환 → `hyp : c = a * b - a * b`
3. `rw [sub_self] at hyp`: `a * b - a * b = 0`이므로 → `hyp : c = 0`
4. `exact hyp`: 목표 `c = 0`과 `hyp : c = 0`이 같으므로 끝!

</details>

---

## 7. 전체 요약: 핵심 개념 한눈에 보기

### 7.1 Lean 4의 핵심 원리

```
모든 것에는 타입이 있다
├── 숫자 3 의 타입은 ℕ (자연수)
├── 함수 f 의 타입은 ℕ → ℕ (자연수를 받아 자연수를 반환)
├── 명제 2+2=4 의 타입은 Prop (참/거짓 판단 가능한 진술)
└── 증명 rfl 의 타입은 2+2=4 (이 명제의 증거)
```

### 7.2 `theorem` vs `lemma` vs `example`

```
theorem (정리)  ─── 이름 ✅, 재사용 ✅, "이것은 중요한 결과!"
lemma (보조정리) ─── 이름 ✅, 재사용 ✅, "이것은 보조 도구!"
example (예시)  ─── 이름 ❌, 재사용 ❌, "연습용 / 데모용"

* Lean 4에서 theorem과 lemma는 기능적으로 완전히 동일하다
```

### 7.3 `rw`(치환/대입/슈퍼포지션) 요약

```
rw [h]          목표에서 h의 왼쪽 → 오른쪽으로 치환
rw [← h]        목표에서 h의 오른쪽 → 왼쪽으로 치환
rw [h] at hyp   가설 hyp에서 치환
rw [h1, h2]     연속 치환

* h는 "A = B" 또는 "A ↔ B" 형태여야 한다
```

### 7.4 `→`(if)와 `↔`(iff)

```
→ (함의, if...then)
  ├── 한 방향만
  ├── 증명: intro로 전제 도입
  └── 사용: apply 또는 직접 적용

↔ (동치, iff)
  ├── 양 방향 (= (→) ∧ (←))
  ├── 분해: .mp (정방향), .mpr (역방향)
  ├── 증명: constructor로 두 방향 각각
  └── 특별: rw에 사용 가능!
```

### 7.5 지금까지 배운 전술(tactic) 목록

| 전술 | 용도 | 예시 |
|------|------|------|
| `rw [h]` | 치환 (바꿔치기) | `rw [mul_comm a b]` |
| `exact h` | "이것이 정확히 증명이다" | `exact hyp` |
| `intro h` | 가정 도입 ("~라고 하자") | `intro h` |
| `apply h` | 정리 적용 | `apply add_le_add` |
| `constructor` | ∧ 또는 ↔ 를 두 목표로 분리 | `constructor` |
| `ring` | 환의 산술 등식 자동 증명 | `ring` |
| `linarith` | 선형 부등식 자동 증명 | `linarith` |
| `sorry` | 미완성 표시 (나중에 채울 것) | `sorry` |

---

## 다음 편 예고

다음 Part 2에서는 **대수적 구조**(Algebraic Structures)에서의 증명을 다룬다:
- **환**(Ring)의 공리와 Lean에서의 표현
- `variable`과 `section`으로 변수 선언 관리하기
- `#check`로 정리 탐색하기
- `nth_rw` — 특정 위치만 치환하기
- `apply`와 `exact`의 심화 사용법

Lean 4의 세계는 넓고 깊다. 하지만 걱정하지 말자 — 지금까지 배운 `rw`, `exact`, `intro`, `apply`만으로도 놀라운 것들을 증명할 수 있다!

> 🎯 **기억하자**: Lean 4에서 증명은 **게임**이다. 목표(goal)가 주어지고, 전술(tactic)이라는 도구로 그 목표를 해결한다. `sorry`로 일단 넘어가고, 나중에 돌아와서 채워도 된다. 즐기면서 하자!
