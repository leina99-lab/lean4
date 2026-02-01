# Lean4 완전 정복 가이드 — 제3편

## 명제(Prop)와 증명의 세계

---

# 제3편: 명제와 증명 완전 정복

---

## 3.1 명제(Prop)란 무엇인가?

### 명제 = 참 또는 거짓인 문장

**명제**(Proposition)는 "참이거나 거짓인 주장"이다.

```
명제인 것:
  "2 + 2 = 4"           → 참인 명제
  "1 = 2"               → 거짓인 명제
  "모든 짝수는 2로 나누어진다" → 참인 명제
  "5는 짝수다"           → 거짓인 명제

명제가 아닌 것:
  "안녕하세요"           → 인사 (참/거짓 없음)
  "밥 먹었니?"           → 질문 (참/거짓 없음)
  "문을 닫아라"          → 명령 (참/거짓 없음)
```

### Lean에서 Prop 타입

```lean
#check 2 + 2 = 4       -- 2 + 2 = 4 : Prop
#check 1 = 2           -- 1 = 2 : Prop
#check 3 < 5           -- 3 < 5 : Prop
```

**결과 읽는 법:**
```
2 + 2 = 4 : Prop
    ↑         ↑
    │         └── 이것의 타입은 Prop(명제)다
    └── 이 표현식은
```

### 중요: 거짓인 명제도 Prop이다!

```lean
#check 1 = 2           -- 1 = 2 : Prop
```

`1 = 2`는 **거짓**이지만, **명제이긴 하다!**

```
비유:
  "지구는 평평하다" → 거짓이지만, 명제는 맞다
  "2 + 2 = 5" → 거짓이지만, 명제는 맞다
  
명제인지 아닌지 ≠ 참인지 거짓인지
```

---

## 3.2 Bool과 Prop의 차이 (매우 중요!)

### 헷갈리기 쉬운 두 개념

| 구분 | **Bool** | **Prop** |
|------|----------|----------|
| **세계** | Type의 세계 (데이터) | Prop의 세계 (논리) |
| **값** | `true`, `false` (딱 2개) | **증명**(proof) |
| **확인 방법** | `#eval`로 계산 | `theorem`으로 증명 |
| **목적** | 프로그램 실행 | 논리적 추론 |

### 예시로 비교

```lean
-- Bool: 계산해서 true/false 얻음
#eval 2 < 3          -- true
#eval 5 == 5         -- true
#eval 10 < 5         -- false
```

```lean
-- Prop: 증명이 필요함
#check (2 < 3 : Prop)      -- 이건 명제
-- #eval (2 < 3 : Prop)    -- 오류! Prop은 계산 불가

-- 증명해야 한다
theorem two_lt_three : 2 < 3 := by decide
```

### 왜 둘 다 필요해?

**Bool은 프로그램용:**
```lean
-- 프로그램에서 조건 분기
def checkAge (age : Nat) : String :=
  if age >= 18 then "성인" else "미성년"

#eval checkAge 20    -- "성인"
#eval checkAge 15    -- "미성년"
```

**Prop은 증명용:**
```lean
-- 수학적 사실을 증명
theorem age_fact : ∀ n : Nat, n + 0 = n := by
  intro n
  rfl
```

### 비유로 이해하기

```
Bool = 계산기
  버튼 누르면 답이 나온다
  "2 < 3이야?" → [계산] → "true!"

Prop = 법정
  판사가 판결을 내려야 한다
  "2 < 3이다" → [증명 제출] → "참으로 인정!"
  
계산기는 빠르지만 단순한 것만 됨
법정은 느리지만 복잡한 것도 됨
```

---

## 3.3 증명이란 무엇인가?

### 증명 = 명제의 "값"

**충격적인 사실**: Lean에서 **증명도 값이다!**

```
일반 프로그래밍:
  타입: Nat
  값: 42

Lean 증명:
  타입: 2 + 2 = 4  (명제가 타입!)
  값: rfl         (증명이 값!)
```

### 코드로 보기

```lean
-- 일반 값
def myNumber : Nat := 42
--     ↑        ↑      ↑
--     │        │      └── 값
--     │        └── 타입
--     └── 이름

-- 증명
theorem myTheorem : 2 + 2 = 4 := rfl
--         ↑            ↑        ↑
--         │            │        └── 증명 (값)
--         │            └── 명제 (타입)
--         └── 이름
```

### 왜 이렇게 설계했을까?

**명제 = 타입, 증명 = 값**이라는 대응 관계를 **커리-하워드 대응**(Curry-Howard Correspondence)이라고 한다.

```
논리학          ↔    프로그래밍
─────────────────────────────
명제           ↔    타입
증명           ↔    값
P → Q          ↔    함수 타입
P ∧ Q          ↔    곱타입 (쌍)
P ∨ Q          ↔    합타입 (Either)
```

이 대응 덕분에 Lean은 **프로그래밍 언어이면서 동시에 증명 시스템**이 될 수 있다!

---

## 3.4 등호(=)와 rfl

### 등호의 의미

`a = b`는 "a와 b가 같다"는 **명제**다.

```lean
#check 2 + 2 = 4     -- 2 + 2 = 4 : Prop
#check 10 = 10       -- 10 = 10 : Prop
#check [1,2] = [1,2] -- [1, 2] = [1, 2] : Prop
```

### rfl: "같은 건 같다"

**rfl**은 **반사성**(reflexivity)의 약자다.

**의미**: "x = x는 당연히 참이다"

```lean
-- 가장 단순한 형태
theorem ten_eq_ten : 10 = 10 := rfl
```

**Lean의 생각 과정:**
```
목표: 10 = 10
rfl 적용: "같은 건 같다"
10과 10은 같으니까 ✓
증명 완료!
```

### rfl이 계산도 해준다

**핵심**: Lean은 rfl을 적용하기 **전에** 양쪽을 **계산**한다!

```lean
theorem ex1 : 2 + 2 = 4 := rfl
```

**Lean의 생각 과정:**
```
목표: 2 + 2 = 4

1단계: 왼쪽을 계산한다
       2 + 2 → 4

2단계: 이제 목표는 4 = 4

3단계: rfl 적용 "같은 건 같다"
       4와 4는 같으니까 ✓

증명 완료!
```

### 더 복잡한 예시

```lean
theorem ex2 : (1 + 2) * 3 = 9 := rfl
```

**Lean의 생각 과정:**
```
목표: (1 + 2) * 3 = 9

1단계: 왼쪽 계산
       (1 + 2) * 3
       = 3 * 3
       = 9

2단계: 이제 목표는 9 = 9

3단계: rfl 적용 ✓
```

```lean
theorem ex3 : [1, 2, 3].length = 3 := rfl
```

**Lean의 생각 과정:**
```
목표: [1, 2, 3].length = 3

1단계: 왼쪽 계산
       [1, 2, 3].length → 3

2단계: 이제 목표는 3 = 3

3단계: rfl 적용 ✓
```

```lean
theorem ex4 : [1, 2] ++ [3] = [1, 2, 3] := rfl
```

**Lean의 생각 과정:**
```
목표: [1, 2] ++ [3] = [1, 2, 3]

1단계: 왼쪽 계산
       [1, 2] ++ [3] → [1, 2, 3]

2단계: 이제 목표는 [1, 2, 3] = [1, 2, 3]

3단계: rfl 적용 ✓
```

### rfl이 안 되는 경우

```lean
-- 이건 오류!
-- theorem ex5 (a b : Nat) : a + b = b + a := rfl
```

**왜 안 될까?**

```
목표: a + b = b + a

1단계: 왼쪽 계산 시도
       a + b → ??? 
       a가 뭔지 모름! 계산 불가!

2단계: 오른쪽 계산 시도
       b + a → ???
       b가 뭔지 모름! 계산 불가!

rfl 적용 불가: 양쪽이 "같은 형태"가 아님
```

**a, b가 변수**이기 때문에 구체적인 계산이 불가능하다!

이런 경우에는 **다른 전술**이 필요하다:

```lean
theorem ex5 (a b : Nat) : a + b = b + a := Nat.add_comm a b
-- 또는
theorem ex5' (a b : Nat) : a + b = b + a := by ring
-- 또는  
theorem ex5'' (a b : Nat) : a + b = b + a := by omega
```

---

## 3.5 theorem vs lemma vs example

### 세 가지 증명 키워드

```lean
-- theorem: 정리 (이름 붙여서 저장)
theorem my_theorem : 2 + 2 = 4 := rfl

-- lemma: 보조정리 (이름 붙여서 저장)
lemma my_lemma : 3 + 3 = 6 := rfl

-- example: 예시 (이름 없이 연습)
example : 4 + 4 = 8 := rfl
```

### theorem과 lemma의 차이

**기능적으로는 완전히 똑같다!**

Lean 입장에서는 `theorem`이나 `lemma`나 차이 없다.

**차이는 인간을 위한 것:**

| 용어 | 의미 | 비유 |
|------|------|------|
| **lemma** | 더 큰 증명을 위한 작은 단계 | 요리의 "재료 손질" |
| **theorem** | 최종적으로 보여주고 싶은 결과 | "완성된 요리" |

```lean
-- 보조정리: 작은 사실
lemma helper : ∀ n : Nat, n + 0 = n := fun n => rfl

-- 정리: 메인 결과 (helper를 사용할 수도 있음)
theorem main : 5 + 0 = 5 := helper 5
```

### example은 언제 쓰나?

**연습할 때!** 이름을 붙일 필요 없이 증명만 확인하고 싶을 때.

```lean
-- 이름 필요 없이 그냥 연습
example : 100 + 0 = 100 := rfl
example : 2 * 3 = 6 := rfl
example : [1,2,3].reverse = [3,2,1] := rfl
```

---

## 3.6 by 키워드와 전술 모드

### 두 가지 증명 방식

Lean에서 증명을 작성하는 방법은 크게 두 가지다:

#### (1) 항 모드(Term Mode) — 직접 증명 값을 적음

```lean
theorem ex1 : 2 + 2 = 4 := rfl
--                       ↑
--                       증명 값을 직접 적음
```

#### (2) 전술 모드(Tactic Mode) — 단계별로 증명

```lean
theorem ex2 : 2 + 2 = 4 := by
  rfl
--                         ↑
--                         전술(tactic)을 사용
```

### by가 뭐야?

`by`는 **"지금부터 전술 모드로 증명하겠다"**는 선언이다.

```lean
theorem my_theorem : 명제 := by
  -- 여기서부터 전술 모드
  -- 전술1
  -- 전술2
  -- ...
```

### 전술(Tactic)이 뭐야?

**전술**(Tactic)은 증명을 한 단계씩 진행하는 **명령어**다.

```
비유:
  요리 레시피 = 전술들의 나열
  
  "파스타 만들기"
  1. 물을 끓인다 (전술 1)
  2. 면을 넣는다 (전술 2)
  3. 8분 기다린다 (전술 3)
  4. 소스를 넣는다 (전술 4)
  5. 완성! 
```

```lean
-- 증명 "레시피"
theorem and_comm (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h        -- 전술 1
  cases h with   -- 전술 2
  | intro hp hq =>
    constructor  -- 전술 3
    · exact hq   -- 전술 4
    · exact hp   -- 전술 5
  -- 완성!
```

### 왜 전술 모드가 필요해?

**복잡한 증명**은 한 줄로 쓰기 어렵다!

```lean
-- 간단한 증명: 항 모드로 충분
theorem simple : 2 + 2 = 4 := rfl

-- 복잡한 증명: 전술 모드가 편함
theorem complex (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  cases h with
  | intro hp hq =>
    constructor
    · exact hq
    · exact hp
```

---

## 3.7 증명 상태(Goal State) 읽는 법

### VS Code에서 보이는 것

전술 모드에서 커서를 움직이면 **증명 상태**가 보인다:

```
1 goal
P Q : Prop
h : P ∧ Q
⊢ Q ∧ P
```

### 읽는 법

```
1 goal            ← 남은 목표 개수
P Q : Prop        ← 컨텍스트: 사용 가능한 것들
h : P ∧ Q         ← 컨텍스트: 가정
⊢ Q ∧ P           ← 목표: 증명해야 할 것
```

**⊢ 기호**: "턴스타일"이라고 읽으며, "증명해야 한다"는 의미

### 전술이 상태를 바꾼다

```lean
theorem and_comm (P Q : Prop) : P ∧ Q → Q ∧ P := by
  -- 초기 상태:
  -- ⊢ P ∧ Q → Q ∧ P
  
  intro h
  -- intro 후 상태:
  -- h : P ∧ Q
  -- ⊢ Q ∧ P
  
  cases h with
  | intro hp hq =>
    -- cases 후 상태:
    -- hp : P
    -- hq : Q
    -- ⊢ Q ∧ P
    
    constructor
    -- constructor 후 상태:
    -- hp : P
    -- hq : Q
    -- ⊢ Q        (첫 번째 목표)
    -- ⊢ P        (두 번째 목표)
    
    · exact hq   -- 첫 번째 목표 해결
    · exact hp   -- 두 번째 목표 해결
```

---

## 3.8 핵심 전술 #1: intro

### intro가 뭐야?

`intro`는 **"가정을 도입한다"**는 전술이다.

### 언제 쓰나?

**목표가 `→` 또는 `∀`로 시작할 때!**

```
목표: P → Q        → intro 사용
목표: ∀ x, P x     → intro 사용
```

### 작동 원리

```lean
example (P Q : Prop) : P → Q → P := by
  -- 상태: ⊢ P → Q → P
  
  intro hp
  -- "P가 참이라고 가정하자. 이 가정을 hp라고 부르자."
  -- 상태: hp : P
  --       ⊢ Q → P
  
  intro hq
  -- "Q가 참이라고 가정하자. 이 가정을 hq라고 부르자."
  -- 상태: hp : P
  --       hq : Q
  --       ⊢ P
  
  exact hp
  -- "hp가 바로 P의 증명이다!"
  -- 증명 완료!
```

### 시각화

```
목표: P → Q → P
      ↓
"P → Q → P를 증명하려면,
 P가 참이라고 가정하고,
 Q가 참이라고 가정한 다음,
 P가 참임을 보이면 된다."
```

```
┌─────────────────────────────────┐
│ 목표: P → Q → P                 │
└─────────────────────────────────┘
              │
              │ intro hp
              ▼
┌─────────────────────────────────┐
│ 가정: hp : P                    │
│ 목표: Q → P                     │
└─────────────────────────────────┘
              │
              │ intro hq
              ▼
┌─────────────────────────────────┐
│ 가정: hp : P                    │
│       hq : Q                    │
│ 목표: P                         │
└─────────────────────────────────┘
              │
              │ exact hp
              ▼
┌─────────────────────────────────┐
│         증명 완료! ✓            │
└─────────────────────────────────┘
```

### 여러 개를 한 번에

```lean
example (P Q : Prop) : P → Q → P := by
  intro hp hq    -- 두 개를 한 번에!
  exact hp
```

### ∀에도 사용

```lean
example : ∀ n : Nat, n = n := by
  intro n        -- "임의의 자연수 n을 잡자"
  rfl            -- "n = n은 당연히 참"
```

**Lean의 생각:**
```
목표: ∀ n : Nat, n = n
      "모든 자연수 n에 대해 n = n이다"

intro n:
      "아무 자연수나 하나 잡아서 n이라고 부르자"
      목표: n = n

rfl:
      "같은 건 같다" ✓
```

---

## 3.9 핵심 전술 #2: exact

### exact가 뭐야?

`exact`는 **"정확히 이것이 증명이다"**라고 말하는 전술이다.

### 언제 쓰나?

**목표와 정확히 일치하는 것이 이미 있을 때!**

```lean
example (P : Prop) (h : P) : P := by
  -- 가정: h : P
  -- 목표: P
  
  exact h
  -- "h가 바로 P의 증명이야!"
```

### exact의 조건

**타입이 정확히 일치해야 한다!**

```lean
example (P : Prop) (h : P) : P := by
  exact h      -- ✓ h의 타입이 P, 목표도 P

-- 이건 안 됨:
-- example (P Q : Prop) (h : P) : Q := by
--   exact h    -- ✗ h의 타입은 P, 목표는 Q (불일치!)
```

### 함수 적용과 함께

```lean
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  -- 가정: h : P → Q
  --       hp : P
  -- 목표: Q
  
  exact h hp
  -- h hp의 타입은?
  -- h : P → Q (P를 받아서 Q를 돌려주는 함수)
  -- hp : P
  -- h hp : Q (함수 h에 hp를 넣으면 Q가 나옴)
  -- 목표와 일치! ✓
```

**Lean의 생각:**
```
h : P → Q  는 "P의 증명을 받으면 Q의 증명을 준다"
hp : P     는 "P의 증명"
h hp : Q   는 "h에 hp를 넣어서 얻은 Q의 증명"

목표가 Q니까, h hp를 제출하면 됨!
```

---

## 3.10 핵심 전술 #3: apply

### apply가 뭐야?

`apply`는 **"이 정리/가정을 적용하겠다"**는 전술이다.

### exact와 뭐가 달라?

- **exact**: 증명을 **완성**할 때 (목표와 정확히 일치)
- **apply**: 증명을 **진행**할 때 (목표를 더 작은 목표로 바꿈)

### 작동 원리

```lean
example (P Q R : Prop) (hpq : P → Q) (hqr : Q → R) (hp : P) : R := by
  -- 가정: hpq : P → Q
  --       hqr : Q → R
  --       hp : P
  -- 목표: R
  
  apply hqr
  -- "hqr : Q → R을 적용하겠다"
  -- "R을 증명하려면 Q를 증명하면 된다"
  -- 목표가 Q로 바뀜!
  
  -- 새 목표: Q
  
  apply hpq
  -- "hpq : P → Q를 적용하겠다"
  -- "Q를 증명하려면 P를 증명하면 된다"
  -- 목표가 P로 바뀜!
  
  -- 새 목표: P
  
  exact hp
  -- hp : P가 목표 P와 일치!
  -- 완료!
```

### 시각화

```
┌─────────────────────────────────┐
│ 목표: R                         │
│ 가정: hqr : Q → R               │
└─────────────────────────────────┘
              │
              │ apply hqr
              │ "R을 얻으려면 Q가 필요해"
              ▼
┌─────────────────────────────────┐
│ 목표: Q                         │
│ 가정: hpq : P → Q               │
└─────────────────────────────────┘
              │
              │ apply hpq
              │ "Q를 얻으려면 P가 필요해"
              ▼
┌─────────────────────────────────┐
│ 목표: P                         │
│ 가정: hp : P                    │
└─────────────────────────────────┘
              │
              │ exact hp
              ▼
┌─────────────────────────────────┐
│         증명 완료! ✓            │
└─────────────────────────────────┘
```

### 비유로 이해하기

```
목표: 케이크를 만들어라 (R)

apply "밀가루 반죽이 있으면 케이크를 만들 수 있다" (Q → R)
→ 새 목표: 밀가루 반죽을 만들어라 (Q)

apply "밀가루가 있으면 반죽을 만들 수 있다" (P → Q)  
→ 새 목표: 밀가루를 구해라 (P)

exact "여기 밀가루가 있다" (P)
→ 완료!
```

---

## 3.11 논리 연산자 ∧ (AND, 그리고)

### ∧의 의미

`P ∧ Q`는 **"P이고 Q이다"**를 의미한다.

```lean
#check (True ∧ True)   -- True ∧ True : Prop
```

**진리표:**
| P | Q | P ∧ Q |
|---|---|-------|
| 참 | 참 | **참** |
| 참 | 거짓 | 거짓 |
| 거짓 | 참 | 거짓 |
| 거짓 | 거짓 | 거짓 |

**P ∧ Q가 참이려면 P와 Q 둘 다 참이어야 한다!**

### ∧ 증명하기: constructor

`P ∧ Q`를 증명하려면, P와 Q를 **각각** 증명해야 한다.

```lean
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  -- 목표: P ∧ Q
  -- 가정: hp : P, hq : Q
  
  constructor
  -- "P ∧ Q를 증명하려면 P와 Q를 각각 증명해야 해"
  -- 목표가 두 개로 나뉨!
  -- 목표 1: P
  -- 목표 2: Q
  
  · -- 목표 1: P
    exact hp
    
  · -- 목표 2: Q
    exact hq
```

### 시각화

```
┌─────────────────────────────────┐
│ 목표: P ∧ Q                     │
│ 가정: hp : P, hq : Q            │
└─────────────────────────────────┘
              │
              │ constructor
              │ "두 부분으로 나눈다"
              ▼
┌─────────────────┐  ┌─────────────────┐
│ 목표 1: P       │  │ 목표 2: Q       │
│ 가정: hp : P    │  │ 가정: hq : Q    │
└─────────────────┘  └─────────────────┘
        │                    │
        │ exact hp           │ exact hq
        ▼                    ▼
┌─────────────────┐  ┌─────────────────┐
│    완료! ✓      │  │    완료! ✓      │
└─────────────────┘  └─────────────────┘
```

### 더 짧은 방법

```lean
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := ⟨hp, hq⟩
```

`⟨hp, hq⟩`는 **익명 생성자**(anonymous constructor)다.

```
⟨hp, hq⟩의 의미:
  "P의 증명 hp와 Q의 증명 hq를 묶어서 P ∧ Q의 증명을 만든다"
```

**입력 방법**: `\<` 와 `\>`

### ∧ 사용하기: cases

`P ∧ Q` 형태의 **가정**이 있으면, 그걸 **분해**해서 P와 Q를 따로 얻을 수 있다.

```lean
example (P Q : Prop) (h : P ∧ Q) : P := by
  -- 목표: P
  -- 가정: h : P ∧ Q
  
  cases h with
  | intro hp hq =>
    -- "h : P ∧ Q를 분해한다"
    -- hp : P
    -- hq : Q
    -- 이제 P와 Q를 따로 쓸 수 있다!
    
    exact hp
```

### 시각화

```
┌─────────────────────────────────┐
│ 목표: P                         │
│ 가정: h : P ∧ Q  (뭉텅이)       │
└─────────────────────────────────┘
              │
              │ cases h with | intro hp hq =>
              │ "h를 분해한다"
              ▼
┌─────────────────────────────────┐
│ 목표: P                         │
│ 가정: hp : P    (P 부분)        │
│       hq : Q    (Q 부분)        │
└─────────────────────────────────┘
              │
              │ exact hp
              ▼
┌─────────────────────────────────┐
│         증명 완료! ✓            │
└─────────────────────────────────┘
```

### 더 짧은 방법: .left, .right 또는 .1, .2

```lean
example (P Q : Prop) (h : P ∧ Q) : P := h.left   -- 또는 h.1
example (P Q : Prop) (h : P ∧ Q) : Q := h.right  -- 또는 h.2
```

### ∧ 완전 예제: 교환법칙

```lean
theorem and_comm (P Q : Prop) : P ∧ Q → Q ∧ P := by
  -- 목표: P ∧ Q → Q ∧ P
  
  intro h
  -- "P ∧ Q가 참이라고 가정하자"
  -- 가정: h : P ∧ Q
  -- 목표: Q ∧ P
  
  cases h with
  | intro hp hq =>
    -- h를 분해
    -- 가정: hp : P, hq : Q
    -- 목표: Q ∧ P
    
    constructor
    -- 목표를 두 개로 나눔
    -- 목표 1: Q
    -- 목표 2: P
    
    · -- 목표 1: Q
      exact hq
      
    · -- 목표 2: P
      exact hp
```

**전체 흐름:**
```
P ∧ Q → Q ∧ P 증명하기

1. P ∧ Q가 참이라고 가정 (intro)
2. P ∧ Q를 P와 Q로 분해 (cases)
3. Q ∧ P를 만들어야 함 (constructor로 나눔)
4. Q 증명: hq 사용 ✓
5. P 증명: hp 사용 ✓
6. 완료!
```

---

## 3.12 논리 연산자 ∨ (OR, 또는)

### ∨의 의미

`P ∨ Q`는 **"P이거나 Q이다"**를 의미한다.

```lean
#check (True ∨ False)   -- True ∨ False : Prop
```

**진리표:**
| P | Q | P ∨ Q |
|---|---|-------|
| 참 | 참 | **참** |
| 참 | 거짓 | **참** |
| 거짓 | 참 | **참** |
| 거짓 | 거짓 | 거짓 |

**P ∨ Q가 참이려면 P나 Q 중 하나만 참이면 된다!**

### ∨ 증명하기: left 또는 right

`P ∨ Q`를 증명하려면, P를 증명하거나 Q를 증명하면 된다.

**left**: 왼쪽(P)을 증명하겠다
**right**: 오른쪽(Q)을 증명하겠다

```lean
example (P Q : Prop) (hp : P) : P ∨ Q := by
  -- 목표: P ∨ Q
  -- 가정: hp : P
  
  left
  -- "왼쪽(P)을 증명하겠다"
  -- 목표: P
  
  exact hp
```

```lean
example (P Q : Prop) (hq : Q) : P ∨ Q := by
  -- 목표: P ∨ Q
  -- 가정: hq : Q
  
  right
  -- "오른쪽(Q)을 증명하겠다"
  -- 목표: Q
  
  exact hq
```

### 시각화

```
P ∨ Q 증명하기 (두 가지 선택)

선택 1: left               선택 2: right
┌──────────────────┐       ┌──────────────────┐
│ 목표: P ∨ Q      │       │ 목표: P ∨ Q      │
└──────────────────┘       └──────────────────┘
         │                          │
         │ left                     │ right
         ▼                          ▼
┌──────────────────┐       ┌──────────────────┐
│ 목표: P          │       │ 목표: Q          │
└──────────────────┘       └──────────────────┘
```

### ∨ 사용하기: cases (경우 나누기)

`P ∨ Q` 형태의 **가정**이 있으면, **두 경우**로 나눠서 처리해야 한다.

"P가 참인 경우"와 "Q가 참인 경우"를 각각 처리!

```lean
example (P Q R : Prop) (h : P ∨ Q) (hp : P → R) (hq : Q → R) : R := by
  -- 목표: R
  -- 가정: h : P ∨ Q
  --       hp : P → R
  --       hq : Q → R
  
  cases h with
  | inl p =>
    -- 경우 1: P가 참인 경우
    -- p : P
    -- 목표: R
    exact hp p    -- hp : P → R에 p : P를 넣으면 R
    
  | inr q =>
    -- 경우 2: Q가 참인 경우  
    -- q : Q
    -- 목표: R
    exact hq q    -- hq : Q → R에 q : Q를 넣으면 R
```

### 시각화

```
┌─────────────────────────────────┐
│ 목표: R                         │
│ 가정: h : P ∨ Q                 │
│       hp : P → R                │
│       hq : Q → R                │
└─────────────────────────────────┘
              │
              │ cases h
              │ "두 경우로 나눈다"
              ▼
      ┌───────┴───────┐
      ▼               ▼
┌───────────────┐ ┌───────────────┐
│ 경우 1: P 참  │ │ 경우 2: Q 참  │
│ p : P         │ │ q : Q         │
│ 목표: R       │ │ 목표: R       │
└───────────────┘ └───────────────┘
      │                   │
      │ exact hp p        │ exact hq q
      ▼                   ▼
┌───────────────┐ ┌───────────────┐
│   완료! ✓     │ │   완료! ✓     │
└───────────────┘ └───────────────┘
```

### 왜 inl과 inr이야?

- **inl** = **in**jection **l**eft (왼쪽에서 왔다)
- **inr** = **in**jection **r**ight (오른쪽에서 왔다)

```
P ∨ Q에서:
  P가 참이면 → inl (왼쪽에서 온 증거)
  Q가 참이면 → inr (오른쪽에서 온 증거)
```

### ∨ 완전 예제: 교환법칙

```lean
theorem or_comm (P Q : Prop) : P ∨ Q → Q ∨ P := by
  -- 목표: P ∨ Q → Q ∨ P
  
  intro h
  -- 가정: h : P ∨ Q
  -- 목표: Q ∨ P
  
  cases h with
  | inl hp =>
    -- 경우 1: P가 참
    -- hp : P
    -- 목표: Q ∨ P
    
    right      -- 오른쪽(P) 증명하겠다
    exact hp   -- hp : P
    
  | inr hq =>
    -- 경우 2: Q가 참
    -- hq : Q
    -- 목표: Q ∨ P
    
    left       -- 왼쪽(Q) 증명하겠다
    exact hq   -- hq : Q
```

---

## 3.13 논리 연산자 → (함축, Implication)

### →의 의미

`P → Q`는 **"P이면 Q이다"**를 의미한다.

```lean
#check (True → False)   -- True → False : Prop
```

**진리표:**
| P | Q | P → Q |
|---|---|-------|
| 참 | 참 | **참** |
| 참 | 거짓 | **거짓** |
| 거짓 | 참 | **참** |
| 거짓 | 거짓 | **참** |

**핵심**: P가 거짓이면, Q가 뭐든 P → Q는 참!

### 왜 P가 거짓이면 항상 참이야?

```
비유: 약속

"내가 복권에 당첨되면, 너한테 100만원 줄게"

경우 1: 복권 당첨 O, 100만원 줌 → 약속 지킴 (참)
경우 2: 복권 당첨 O, 100만원 안 줌 → 약속 어김 (거짓)
경우 3: 복권 당첨 X → 약속이 발동 안 됨! (참으로 간주)
경우 4: 복권 당첨 X → 약속이 발동 안 됨! (참으로 간주)

복권에 당첨되지 않으면 약속을 어긴 것도 아니고 지킨 것도 아님.
논리학에서는 이런 경우를 "참"으로 정한다.
```

### → 증명하기: intro

`P → Q`를 증명하려면:
1. P가 참이라고 **가정**한다
2. 그 가정 하에 Q가 참임을 보인다

```lean
example (P : Prop) : P → P := by
  -- 목표: P → P
  
  intro hp
  -- "P가 참이라고 가정하자. 이를 hp라 부르자."
  -- 가정: hp : P
  -- 목표: P
  
  exact hp
  -- hp가 바로 P의 증명!
```

### → 사용하기: apply 또는 직접 적용

`P → Q` 형태의 가정이 있고, P의 증명이 있으면, Q를 얻을 수 있다.

```lean
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  -- 가정: h : P → Q
  --       hp : P
  -- 목표: Q
  
  apply h
  -- "h : P → Q를 적용한다"
  -- "Q를 얻으려면 P가 필요하다"
  -- 목표: P
  
  exact hp
```

또는 더 짧게:

```lean
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  exact h hp    -- h에 hp를 넣으면 Q
```

또는 항 모드로:

```lean
example (P Q : Prop) (h : P → Q) (hp : P) : Q := h hp
```

### →는 함수다!

**핵심 통찰**: `P → Q`는 "P의 증명을 받아서 Q의 증명을 반환하는 **함수**"다!

```
커리-하워드 대응:
  P → Q (명제) ↔ P를 받아서 Q를 주는 함수 (타입)
  
h : P → Q 는
  "P의 증명을 주면 Q의 증명을 돌려주는 함수"

hp : P 는
  "P의 증명"

h hp : Q 는
  "함수 h에 hp를 넣어서 얻은 Q의 증명"
```

---

## 3.14 논리 연산자 ↔ (동치, If and Only If)

### ↔의 의미

`P ↔ Q`는 **"P일 때 그리고 그때만 Q"**를 의미한다.

다른 말로: **(P → Q) ∧ (Q → P)**

```lean
#check (True ↔ True)   -- True ↔ True : Prop
```

**진리표:**
| P | Q | P ↔ Q |
|---|---|-------|
| 참 | 참 | **참** |
| 참 | 거짓 | 거짓 |
| 거짓 | 참 | 거짓 |
| 거짓 | 거짓 | **참** |

**P ↔ Q가 참이려면 P와 Q의 진리값이 같아야 한다!**

### → vs ↔ 비교

| 특성 | **→** (함축) | **↔** (동치) |
|------|-------------|-------------|
| 방향 | 한 방향 | 양방향 |
| 의미 | "P이면 Q" | "P일 때 그리고 그때만 Q" |
| 분해 | 불가 | `.mp`, `.mpr`로 분해 가능 |
| `rw` 사용 | **불가** | **가능!** |

### ↔ 증명하기: constructor

`P ↔ Q`를 증명하려면, **양방향** 모두 증명해야 한다:
- P → Q (정방향)
- Q → P (역방향)

```lean
example (P : Prop) : P ↔ P := by
  -- 목표: P ↔ P
  
  constructor
  -- 목표를 두 개로 나눔
  -- 목표 1: P → P (정방향)
  -- 목표 2: P → P (역방향)
  
  · -- 목표 1: P → P
    intro hp
    exact hp
    
  · -- 목표 2: P → P
    intro hp
    exact hp
```

### 시각화

```
┌─────────────────────────────────┐
│ 목표: P ↔ Q                     │
│       = (P → Q) ∧ (Q → P)       │
└─────────────────────────────────┘
              │
              │ constructor
              ▼
┌─────────────────┐  ┌─────────────────┐
│ 목표 1: P → Q   │  │ 목표 2: Q → P   │
│ (정방향)        │  │ (역방향)        │
└─────────────────┘  └─────────────────┘
```

### ↔ 사용하기: .mp, .mpr

`P ↔ Q` 형태의 가정이 있으면, 각 방향을 **추출**할 수 있다.

```lean
example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  -- 가정: h : P ↔ Q
  --       hp : P
  -- 목표: Q
  
  exact h.mp hp
  -- h.mp : P → Q (정방향)
  -- h.mp hp : Q
```

```lean
example (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := by
  -- 가정: h : P ↔ Q
  --       hq : Q
  -- 목표: P
  
  exact h.mpr hq
  -- h.mpr : Q → P (역방향)
  -- h.mpr hq : P
```

**mp와 mpr의 의미:**
- **mp** = modus ponens (정방향)
- **mpr** = modus ponens reverse (역방향)

또는 `.1`, `.2`로도 사용 가능:
```lean
example (P Q : Prop) (h : P ↔ Q) : P → Q := h.1
example (P Q : Prop) (h : P ↔ Q) : Q → P := h.2
```

### ↔로 치환하기: rw

**이것이 ↔의 강력한 점!**

`P ↔ Q`가 있으면, 목표나 가정에서 P를 Q로 (또는 Q를 P로) **바꿀 수 있다!**

```lean
example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  -- 가정: h : P ↔ Q
  --       hp : P
  -- 목표: Q
  
  rw [← h]
  -- h : P ↔ Q를 역방향으로 적용
  -- 목표의 Q를 P로 바꿈
  -- 목표: P
  
  exact hp
```

```lean
example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  rw [h] at hp
  -- 가정 hp에서 P를 Q로 바꿈
  -- hp : Q
  -- 목표: Q
  
  exact hp
```

**주의**: `→`로는 `rw`를 쓸 수 없다! `↔`만 가능!

```lean
-- 이건 안 됨!
-- example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
--   rw [h] at hp   -- 오류! →는 rw에 쓸 수 없음
```

---

## 3.15 논리 연산자 ¬ (부정, Negation)

### ¬의 의미

`¬P`는 **"P가 아니다"**를 의미한다.

**정의**: `¬P`는 `P → False`와 같다!

```lean
#check (¬ True)    -- ¬True : Prop
#check (¬ False)   -- ¬False : Prop
```

### 왜 ¬P = P → False야?

```
"P가 아니다"
= "P가 참이면 모순이다"
= "P가 참이면 False다"
= P → False
```

**비유:**
```
"이 방에 코끼리가 없다"
= "코끼리가 있다고 가정하면 모순이 생긴다"
= "코끼리가 있다 → 불가능"
```

### ¬ 증명하기: intro

`¬P` = `P → False`이므로, **P를 가정하고 모순을 도출**하면 된다!

```lean
example (P : Prop) (h : P → False) : ¬P := by
  -- 목표: ¬P = P → False
  -- 가정: h : P → False
  
  intro hp
  -- P가 참이라고 가정
  -- 가정: hp : P
  -- 목표: False
  
  exact h hp
  -- h hp : False
```

### ¬ 사용하기

`¬P`와 `P`가 둘 다 있으면, **모순**이 생긴다!

```lean
example (P : Prop) (hp : P) (hnp : ¬P) : False := by
  -- 가정: hp : P
  --       hnp : ¬P = P → False
  -- 목표: False
  
  exact hnp hp
  -- hnp : P → False에 hp : P를 넣으면 False
```

### absurd 사용하기

```lean
example (P Q : Prop) (hp : P) (hnp : ¬P) : Q := by
  exact absurd hp hnp
  -- absurd : P → ¬P → Q
  -- "P와 ¬P가 동시에 있으면 무엇이든 증명할 수 있다"
```

**"거짓에서는 모든 것이 따라 나온다"** (ex falso quodlibet)

---

## 3.16 양화사 ∀ (전칭, For All)

### ∀의 의미

`∀ x, P x`는 **"모든 x에 대해 P(x)가 성립한다"**를 의미한다.

```lean
#check (∀ n : Nat, n = n)     -- ∀ (n : Nat), n = n : Prop
#check (∀ n : Nat, n + 0 = n) -- ∀ (n : Nat), n + 0 = n : Prop
```

### ∀ 증명하기: intro

`∀ x, P x`를 증명하려면, **임의의 x를 잡고** P(x)를 증명한다.

```lean
example : ∀ n : Nat, n = n := by
  -- 목표: ∀ n : Nat, n = n
  
  intro n
  -- "임의의 자연수 n을 잡자"
  -- 가정: n : Nat
  -- 목표: n = n
  
  rfl
  -- 같은 건 같다 ✓
```

**Lean의 생각:**
```
"모든 자연수 n에 대해 n = n임을 보여라"

intro n:
  "아무 자연수나 하나 골라서 n이라고 부르자.
   이 n에 대해 n = n임을 보이면,
   n이 아무거나였으니 모든 자연수에 대해 성립!"
```

### ∀ 사용하기: 직접 적용

`∀ x, P x` 형태의 가정이 있으면, **구체적인 값**에 적용할 수 있다.

```lean
example (h : ∀ n : Nat, n + 0 = n) : 5 + 0 = 5 := by
  -- 가정: h : ∀ n : Nat, n + 0 = n
  -- 목표: 5 + 0 = 5
  
  exact h 5
  -- h 5 : 5 + 0 = 5
  -- "h를 n = 5에 적용"
```

### ∀는 함수다!

**핵심 통찰**: `∀ x : α, P x`는 "x를 받아서 P(x)의 증명을 주는 **함수**"다!

```
h : ∀ n : Nat, n + 0 = n

이건 "아무 자연수 n을 주면, n + 0 = n의 증명을 돌려주는 함수"

h 5 : 5 + 0 = 5
h 100 : 100 + 0 = 100
h 0 : 0 + 0 = 0
```

### 여러 ∀

```lean
example : ∀ (a b : Nat), a + b = b + a := by
  intro a
  intro b
  -- 또는: intro a b
  exact Nat.add_comm a b
```

---

## 3.17 양화사 ∃ (존재, There Exists)

### ∃의 의미

`∃ x, P x`는 **"P(x)를 만족하는 x가 존재한다"**를 의미한다.

```lean
#check (∃ n : Nat, n > 0)     -- ∃ n, n > 0 : Prop
#check (∃ n : Nat, n = n + 1) -- ∃ n, n = n + 1 : Prop (거짓이지만 명제는 맞음)
```

### ∃ 증명하기: use

`∃ x, P x`를 증명하려면, **구체적인 예시**를 보여주면 된다!

```lean
example : ∃ n : Nat, n > 0 := by
  -- 목표: ∃ n : Nat, n > 0
  
  use 1
  -- "n = 1을 쓰겠다"
  -- 목표: 1 > 0
  
  decide
  -- 1 > 0은 계산으로 확인 가능 ✓
```

**Lean의 생각:**
```
"0보다 큰 자연수가 존재함을 보여라"

use 1:
  "1이 그 예시다"
  "1 > 0임을 보이면 됨"

decide:
  1 > 0? 계산해보니 true! ✓
```

### 또 다른 예시

```lean
example : ∃ n : Nat, n * n = 4 := by
  use 2
  -- 목표: 2 * 2 = 4
  rfl
  -- 2 * 2 = 4 계산으로 확인 ✓
```

### ∃ 사용하기: cases 또는 obtain

`∃ x, P x` 형태의 **가정**이 있으면, 그 x와 P(x)의 증명을 **꺼낼 수 있다**.

```lean
example (h : ∃ n : Nat, n > 0) : True := by
  -- 가정: h : ∃ n : Nat, n > 0
  -- 목표: True
  
  cases h with
  | intro n hn =>
    -- n : Nat       (그 존재하는 값)
    -- hn : n > 0    (그 값에 대한 성질)
    trivial
```

더 편한 방법: `obtain`

```lean
example (h : ∃ n : Nat, n > 0) : True := by
  obtain ⟨n, hn⟩ := h
  -- n : Nat
  -- hn : n > 0
  trivial
```

### ∃와 ∀의 관계

```
∀ n, P n  = "모든 n에 대해 P(n)이 참"
∃ n, P n  = "P(n)이 참인 n이 적어도 하나 있다"

부정하면:
¬(∀ n, P n) ↔ ∃ n, ¬P n
  "모두가 P를 만족하는 건 아니다" ↔ "P를 만족하지 않는 게 있다"

¬(∃ n, P n) ↔ ∀ n, ¬P n
  "P를 만족하는 게 없다" ↔ "모두가 P를 만족하지 않는다"
```

---

## 3.18 증명 연습: 종합 예제

### 예제 1: 기본 함축

```lean
-- "P이면 P이다"
theorem impl_refl (P : Prop) : P → P := by
  intro hp      -- P를 가정
  exact hp      -- 그게 바로 증명
```

### 예제 2: 함축의 연쇄

```lean
-- "P → Q이고 Q → R이면, P → R이다"
theorem impl_trans (P Q R : Prop) (hpq : P → Q) (hqr : Q → R) : P → R := by
  intro hp      -- P를 가정
  -- 가정: hp : P
  -- 목표: R
  
  apply hqr     -- R을 얻으려면 Q가 필요
  -- 목표: Q
  
  apply hpq     -- Q를 얻으려면 P가 필요
  -- 목표: P
  
  exact hp      -- hp가 P의 증명
```

### 예제 3: And 분해와 재조립

```lean
-- "P ∧ Q이면 Q ∧ P이다"
theorem and_comm' (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h           -- P ∧ Q를 가정
  cases h with
  | intro hp hq =>  -- P와 Q로 분해
    constructor     -- Q ∧ P를 만들어야 함
    · exact hq      -- 첫 번째: Q
    · exact hp      -- 두 번째: P
```

### 예제 4: Or 경우 나누기

```lean
-- "P ∨ Q이면 Q ∨ P이다"
theorem or_comm' (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h           -- P ∨ Q를 가정
  cases h with
  | inl hp =>       -- 경우 1: P가 참
    right           -- Q ∨ P에서 오른쪽(P) 선택
    exact hp
  | inr hq =>       -- 경우 2: Q가 참
    left            -- Q ∨ P에서 왼쪽(Q) 선택
    exact hq
```

### 예제 5: 전칭과 존재

```lean
-- "모든 n에 대해 P(n)이면, P(n)인 n이 존재한다" (단, Nat은 비어있지 않음)
theorem forall_implies_exists (P : Nat → Prop) (h : ∀ n, P n) : ∃ n, P n := by
  use 0           -- n = 0을 예시로 사용
  exact h 0       -- h 0 : P 0
```

### 예제 6: 동치의 대칭성

```lean
-- "P ↔ Q이면 Q ↔ P이다"
theorem iff_comm' (P Q : Prop) : (P ↔ Q) → (Q ↔ P) := by
  intro h         -- P ↔ Q를 가정
  constructor     -- Q ↔ P를 만들어야 함
  · -- Q → P
    exact h.mpr   -- h.mpr : Q → P
  · -- P → Q
    exact h.mp    -- h.mp : P → Q
```

---

## 3.19 전술 요약 카드

### 목표 변경 전술

| 전술 | 목표 형태 | 하는 일 |
|------|----------|--------|
| `intro x` | `P → Q` 또는 `∀ x, P` | 가정 도입, 목표 축소 |
| `constructor` | `P ∧ Q` 또는 `P ↔ Q` | 목표를 여러 개로 나눔 |
| `left` | `P ∨ Q` | 왼쪽(P) 증명 선택 |
| `right` | `P ∨ Q` | 오른쪽(Q) 증명 선택 |
| `use a` | `∃ x, P x` | 구체적 예시 제공 |
| `rfl` | `a = a` | 반사성으로 완료 |

### 가정 사용 전술

| 전술 | 가정 형태 | 하는 일 |
|------|----------|--------|
| `exact h` | 목표와 일치 | 증명 완료 |
| `apply h` | `A → B` (목표가 B) | 목표를 A로 변경 |
| `cases h` | `P ∧ Q` 또는 `P ∨ Q` | 가정 분해 |
| `rw [h]` | `a = b` 또는 `P ↔ Q` | 치환 |

---

## 3.20 연습 문제

### 문제 1: 기본 함축

```lean
-- "P이고 Q이면, P이다"
theorem ex1 (P Q : Prop) : P ∧ Q → P := by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
theorem ex1 (P Q : Prop) : P ∧ Q → P := by
  intro h
  cases h with
  | intro hp hq => exact hp
-- 또는 더 짧게:
-- theorem ex1 (P Q : Prop) : P ∧ Q → P := fun h => h.1
```
</details>

### 문제 2: Or 도입

```lean
-- "P이면, P이거나 Q이다"
theorem ex2 (P Q : Prop) : P → P ∨ Q := by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
theorem ex2 (P Q : Prop) : P → P ∨ Q := by
  intro hp
  left
  exact hp
```
</details>

### 문제 3: 연쇄 함축

```lean
-- "P → Q이고 P이면, Q이다"
theorem ex3 (P Q : Prop) : (P → Q) → P → Q := by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
theorem ex3 (P Q : Prop) : (P → Q) → P → Q := by
  intro hpq
  intro hp
  exact hpq hp
-- 또는 더 짧게:
-- theorem ex3 (P Q : Prop) : (P → Q) → P → Q := fun hpq hp => hpq hp
```
</details>

### 문제 4: 존재 양화사

```lean
-- "10보다 큰 자연수가 존재한다"
theorem ex4 : ∃ n : Nat, n > 10 := by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
theorem ex4 : ∃ n : Nat, n > 10 := by
  use 11
  decide
-- 또는: use 100, use 42 등 아무 11 이상의 수
```
</details>

### 문제 5: 종합

```lean
-- "P ∧ (Q ∧ R) 이면 (P ∧ Q) ∧ R 이다"
theorem ex5 (P Q R : Prop) : P ∧ (Q ∧ R) → (P ∧ Q) ∧ R := by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
theorem ex5 (P Q R : Prop) : P ∧ (Q ∧ R) → (P ∧ Q) ∧ R := by
  intro h
  cases h with
  | intro hp hqr =>
    cases hqr with
    | intro hq hr =>
      constructor
      · constructor
        · exact hp
        · exact hq
      · exact hr
```
</details>

---

## 다음 편 예고

**제4편: 치환과 계산**에서는:
- `rw` 전술 심화
- `simp` 전술
- `ring`, `omega`, `linarith` 전술
- `calc` 모드

를 자세히 다룬다.
