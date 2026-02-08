# Part 15-A: 형식 언어와 문법 — 계산 모델의 첫걸음

> **Rosen 이산수학 8판 · Chapter 13 (Section 13.1) 기반**
> **Lean 4 형식화 + 3단계 연습문제**

---

## 0. 들어가며: 이 파트에서 배울 것

컴퓨터는 "이 프로그램이 문법적으로 올바른가?"를 어떻게 판단할까? 사람이 "The frog writes neatly"가 올바른 영어 문장인지 판단하듯, 컴퓨터도 프로그래밍 언어의 **문법 규칙**을 사용하여 코드의 올바름을 판단한다.

이 파트에서는 **형식 언어**(formal language)와 **문법**(grammar)의 수학적 정의를 배우고, 이것을 Lean 4로 형식화하는 방법을 익힌다.

### 다루는 내용

1. **어휘**(vocabulary)와 **언어**(language)의 정의
2. **구-구조 문법**(phrase-structure grammar) — 문자열을 만드는 규칙
3. **유도**(derivation) — 시작 기호로부터 문자열 생성
4. **촘스키 위계**(Chomsky hierarchy) — 문법의 4가지 유형
5. **BNF 형식**(Backus-Naur Form) — 프로그래밍 언어의 문법 표기법
6. **유도 트리**(derivation tree / parse tree)
7. Lean 4로 형식 언어와 문법을 모델링하는 방법

> 💡 **왜 배우나?** 컴파일러, 정규 표현식, XML/HTML 파서, 자연어 처리 — 이 모든 것의 이론적 기초가 형식 언어와 문법이다. 프로그래밍을 하면서 "syntax error"를 본 적이 있다면, 이미 형식 문법과 만난 것이다!

---

## 1. 어휘와 언어 — 기호, 문자열, 언어

### 1.1 **어휘**(Vocabulary)란?

> **정의 1** (Rosen 정의 1)
> **어휘**(vocabulary) 또는 **알파벳**(alphabet) V는 **기호**(symbol)라 부르는 원소들의 **공집합이 아닌 유한집합**이다.

쉽게 말해, 어휘는 "사용할 수 있는 글자 모음"이다.

**예시:**
- 이진수의 어휘: V = {0, 1}
- 영어 소문자의 어휘: V = {a, b, c, ..., z}
- 프로그래밍 언어의 어휘: V = {if, else, while, {, }, (, ), ;, ...}
- DNA의 어휘: V = {A, T, G, C}

### 1.2 **단어**(Word)와 **문자열**(String)

> **정의** : V에서 정의된 **단어**(word) 또는 **문장**(sentence)은 집합 V의 원소로 구성된 **유한 길이의 문자열**이다.

| 어휘 V = {0, 1} | 만들 수 있는 단어 예시 |
|---|---|
| 길이 0 | λ (공 문자열) |
| 길이 1 | 0, 1 |
| 길이 2 | 00, 01, 10, 11 |
| 길이 3 | 000, 001, 010, 011, 100, 101, 110, 111 |

#### **공 문자열**(empty string) λ

**공 문자열**(empty string) λ는 **길이가 0**인 문자열이다. 아무 기호도 포함하지 않는다.

> ⚠️ **주의**: 공 문자열 λ와 공집합 ∅는 다르다!
> - λ는 **문자열**이다 (내용이 없는 문자열)
> - ∅는 **집합**이다 (원소가 없는 집합)
> - {λ}는 "공 문자열 하나를 원소로 가진 집합"이다 (원소가 1개!)

비유하면: λ는 "빈 종이"이고, ∅는 "종이가 아예 없는 것"이다. 빈 종이는 여전히 종이이다!

#### V* — 모든 단어의 집합

> **표기법**: V에서 정의된 **모든 단어들의 집합**을 **V***로 표시한다.

예를 들어, V = {0, 1}이면:
- V* = {λ, 0, 1, 00, 01, 10, 11, 000, 001, ..., 0110, ...}

V*는 **무한집합**이다! V가 아무리 작아도 (심지어 {0} 하나뿐이어도), V*는 무한하다.

### 1.3 **언어**(Language)의 정의

> **정의** : V에서 정의된 **언어**(language)는 V*의 **부분집합**이다.

언어 = "허용되는 단어들의 모음"이다. V*의 모든 단어 중에서 **특정 규칙을 만족하는 것들만 골라낸** 집합이 언어이다.

**예시:**
| 어휘 | 언어 | 설명 |
|------|------|------|
| {0, 1} | {0, 01, 011, 0111, ...} | 0 다음에 1이 0개 이상 |
| {0, 1} | {λ, 01, 0011, 000111, ...} | 0ⁿ1ⁿ (n ≥ 0) |
| {a, b} | {aba, abba, abbba, ...} | a 다음에 b 1개 이상 다음에 a |
| {0, 1} | ∅ | 빈 언어 (아무 단어도 없음) |
| {0, 1} | {λ} | 공 문자열만 포함하는 언어 |

### 1.4 Lean 4에서의 모델링

Lean 4에서 어휘와 언어를 모델링하는 가장 자연스러운 방법은 **리스트**(List)를 사용하는 것이다:

```lean
-- 어휘의 원소를 나타내는 타입
inductive Symbol where
  | zero : Symbol    -- 기호 '0'
  | one  : Symbol    -- 기호 '1'
  deriving DecidableEq, Repr

-- 문자열 = 기호의 리스트
-- "01" 은 [Symbol.zero, Symbol.one]
-- λ (공 문자열)은 []
def Word := List Symbol

-- 언어 = 문자열의 집합 (문자열 → 참/거짓 함수)
def Language := Word → Prop
```

몇 가지 언어의 예:

```lean
-- 빈 언어: 아무 단어도 포함하지 않는다
def emptyLang : Language := fun _ => False

-- {λ} 언어: 공 문자열만 포함
def lambdaLang : Language := fun w => w = []

-- 모든 문자열의 언어 (= V*)
def allWords : Language := fun _ => True

-- 길이가 2인 문자열의 언어
def lengthTwo : Language := fun w => w.length = 2
```

---

## 2. 구-구조 문법 — 문자열을 만드는 규칙

### 2.1 직관적 이해: 영어 문법의 예

형식적인 정의에 들어가기 전에, 영어 문법의 예를 통해 직관을 잡자.

다음 규칙으로 간단한 영어 문장을 만들 수 있다:

| 규칙 번호 | 규칙 | 설명 |
|-----------|------|------|
| 1 | 문장 → 명사구 동사구 | 문장 = 명사구 + 동사구 |
| 2 | 명사구 → 관사 형용사 명사 | 관사 + 형용사 + 명사 |
| 3 | 명사구 → 관사 명사 | 관사 + 명사 (형용사 생략) |
| 4 | 동사구 → 동사 부사 | 동사 + 부사 |
| 5 | 동사구 → 동사 | 동사만 |
| 6~7 | 관사 → a \| the | |
| 8~9 | 형용사 → large \| hungry | |
| 10~11 | 명사 → rabbit \| mathematician | |
| 12~13 | 동사 → eats \| hops | |
| 14~15 | 부사 → quickly \| wildly | |

이 규칙으로 "the large rabbit hops quickly"를 만드는 과정:

```
문장
→ 명사구 동사구                    (규칙 1)
→ 관사 형용사 명사 동사구           (규칙 2)
→ the 형용사 명사 동사구            (규칙 7)
→ the large 명사 동사구             (규칙 8)
→ the large rabbit 동사구           (규칙 10)
→ the large rabbit 동사 부사        (규칙 4)
→ the large rabbit hops 부사        (규칙 13)
→ the large rabbit hops quickly     (규칙 14)  ✅ 완성!
```

여기서 핵심 개념:
- **"문장", "명사구", "동사구"** 등은 다른 것으로 **바뀔 수 있는** 기호 → **비단말 기호**(nonterminal)
- **"the", "rabbit", "hops"** 등은 더 이상 바뀌지 않는 **최종 결과** → **단말 기호**(terminal)
- 각 규칙 (예: 문장 → 명사구 동사구)을 **생성**(production)이라 부른다
- 시작점인 "문장"을 **시작 기호**(start symbol)라 부른다

### 2.2 형식적 정의

> **정의 2** (Rosen 정의 2)
> **구-구조 문법**(phrase-structure grammar) G = (V, T, S, P)는 다음으로 구성된다:
> - **V**: **어휘**(vocabulary) — 모든 기호의 유한집합
> - **T**: **단말 기호**(terminal) — V의 부분집합. 더 이상 바뀌지 않는 "최종" 기호
> - **S**: **시작 기호**(start symbol) — V에 속하는 특별한 비단말 기호. 모든 유도의 출발점
> - **P**: **생성**(production)의 유한집합 — "이것을 저것으로 바꿔라"는 규칙

**비단말 기호**(nonterminal) N = V - T 이다. 즉, 어휘에서 단말을 뺀 나머지가 비단말이다.

생성은 **w₀ → w₁** 형태이며, **w₀에는 반드시 비단말 기호가 최소 한 개** 포함되어야 한다. (순수 단말 기호만으로 된 문자열에서는 더 이상 치환할 것이 없으므로, 생성의 왼쪽이 될 수 없다.)

### 2.3 구체적 예제들

#### 예제 1 (Rosen 예제 1)

다음 문법이 구-구조 문법인지 확인하라:

G = (V, T, S, P)에서
- V = {a, b, A, B, S}
- T = {a, b}
- S는 시작 기호
- P = {S → ABa, A → BB, B → ab, AB → b}

**확인:**
- V는 공집합이 아닌 유한집합 ✅
- T = {a, b} ⊆ V ✅
- N = V - T = {A, B, S} ✅
- S ∈ N ✅
- 모든 생성의 왼쪽에 비단말 포함:
  - S → ABa: 왼쪽에 S(비단말) ✅
  - A → BB: 왼쪽에 A(비단말) ✅
  - B → ab: 왼쪽에 B(비단말) ✅
  - AB → b: 왼쪽에 A, B(비단말) ✅

따라서 구-구조 문법이다! ✅

#### 예제 2 (Rosen 예제 3): 문법이 생성하는 언어 구하기

V = {S, A, a, b}, T = {a, b}, 시작 기호 S, P = {S → aA, S → b, A → aa}

**풀이:**
- S에서 출발:
  - S → b (단말 문자열 "b" 완성) ✅
  - S → aA → a(aa) = aaa (단말 문자열 "aaa" 완성) ✅
  - 더 이상 유도할 수 있는 문자열이 없다

따라서 **L(G) = {b, aaa}** 이다.

#### 예제 3 (Rosen 예제 4): 무한 언어 생성

V = {S, 0, 1}, T = {0, 1}, 시작 기호 S, P = {S → 11S, S → 0}

**풀이:**
- S → 0: "0"
- S → 11S → 110: "110"
- S → 11S → 1111S → 11110: "11110"
- S → 11S → 1111S → 111111S → 1111110: "1111110"
- ...

패턴: **짝수 개의 1 다음에 0**이 온다!

**L(G) = {0, 110, 11110, 1111110, ...} = {1²ⁿ0 | n ≥ 0}**

> 💡 "11S"는 S 앞에 11을 두 개 붙이는 효과이고, "0"은 유도를 멈추는 효과이다. S → 11S를 n번 반복한 후 S → 0으로 끝내면 1²ⁿ0이 된다.

#### 예제 4 (Rosen 예제 5): 유명한 언어 {0ⁿ1ⁿ}

**문제**: 집합 {0ⁿ1ⁿ | n = 0, 1, 2, ...} = {λ, 01, 0011, 000111, ...}을 생성하는 문법을 구하라.

**풀이:** G = (V, T, S, P)에서
- V = {0, 1, S}, T = {0, 1}
- P = {S → 0S1, S → λ}

검증:
- n=0: S → λ ✅
- n=1: S → 0S1 → 0λ1 = 01 ✅
- n=2: S → 0S1 → 00S11 → 00λ11 = 0011 ✅
- n=3: S → 0S1 → 00S11 → 000S111 → 000λ111 = 000111 ✅

> 💡 S → 0S1의 핵심: S의 **양쪽**에 0과 1을 하나씩 추가한다. 이렇게 하면 0의 개수와 1의 개수가 항상 같게 유지된다!

### 2.4 Lean 4로 문법 모델링

```lean
-- 기호 타입: 단말 또는 비단말
inductive GSymbol (T : Type) (N : Type) where
  | terminal    : T → GSymbol T N
  | nonterminal : N → GSymbol T N
  deriving DecidableEq, Repr

-- 생성 규칙: 왼쪽 문자열 → 오른쪽 문자열
structure Production (T : Type) (N : Type) where
  lhs : List (GSymbol T N)    -- 왼쪽 (비단말 최소 1개 포함)
  rhs : List (GSymbol T N)    -- 오른쪽

-- 구-구조 문법
structure Grammar (T : Type) (N : Type) where
  start : N                           -- 시작 기호
  productions : List (Production T N) -- 생성 규칙의 리스트
```

{0ⁿ1ⁿ} 문법을 Lean 4로 구현:

```lean
-- 단말 기호
inductive Bit where | b0 | b1
  deriving DecidableEq, Repr

-- 비단말 기호
inductive NT01 where | S
  deriving DecidableEq, Repr

open GSymbol in
-- 문법: S → 0S1, S → λ
def grammar_0n1n : Grammar Bit NT01 := {
  start := NT01.S
  productions := [
    -- S → 0S1
    { lhs := [nonterminal NT01.S],
      rhs := [terminal Bit.b0, nonterminal NT01.S, terminal Bit.b1] },
    -- S → λ (빈 리스트)
    { lhs := [nonterminal NT01.S],
      rhs := [] }
  ]
}
```

---

## 3. 유도 — 시작 기호에서 문자열까지

### 3.1 직접 유도 (⇒)

> **정의 3** (Rosen 정의 3)
> w₀ = lz₀r (즉, l, z₀, r의 연결)이고, z₀ → z₁이 문법 G의 생성이라 하면, w₁ = lz₁r은 w₀에서 **직접 유도**(directly derivable)될 수 있다고 하고, **w₀ ⇒ w₁**로 표기한다.

쉽게 말해: 문자열 안에서 생성 규칙의 왼쪽을 찾아 오른쪽으로 **바꾸는** 것이 직접 유도이다.

**예:** 문법 P = {B → ab}에서
- A**B**a에서 B를 ab로 바꾸면 → A**ab**a
- 따라서 ABa ⇒ Aaba

### 3.2 유도 (⇒*)

> **정의**: w₀ ⇒ w₁ ⇒ w₂ ⇒ ... ⇒ wₙ 이면, wₙ은 w₀에서 **유도**(derivable)될 수 있다고 하고, **w₀ ⇒* wₙ**으로 표기한다.

즉, 여러 번의 직접 유도를 연쇄하는 것이다.

**예** (Rosen 예제 2): 예제 1의 문법에서

```
ABa ⇒ Aaba       (B → ab)
    ⇒ BBaba      (A → BB)
    ⇒ Bababa     (B → ab)
    ⇒ abababa    (B → ab)
```

따라서 ABa ⇒* abababa

### 3.3 문법이 생성하는 언어 L(G)

> **정의 4** (Rosen 정의 4)
> 문법 G = (V, T, S, P)에 의해 **생성된 언어**(language generated by G) L(G)는:
>
> **L(G) = {w ∈ T* | S ⇒* w}**
>
> 즉, 시작 기호 S로부터 유도될 수 있는 **모든 단말 문자열**들의 집합이다.

핵심:
1. **S에서 시작**해야 한다
2. 유도 결과가 **단말 기호만**으로 이루어져야 한다 (비단말이 남아있으면 안 됨)
3. 유도 과정에서 어떤 생성을, 몇 번 사용하든 상관없다

### 3.4 Lean 4로 유도 모델링

```lean
-- 직접 유도: 한 번의 생성 적용
inductive DirectDerivation {T N : Type} [DecidableEq T] [DecidableEq N]
    (G : Grammar T N) : List (GSymbol T N) → List (GSymbol T N) → Prop where
  | step : ∀ (p : Production T N) (l r : List (GSymbol T N)),
      p ∈ G.productions →
      DirectDerivation G (l ++ p.lhs ++ r) (l ++ p.rhs ++ r)

-- 유도 (⇒*): 직접 유도의 반사적 전이적 폐쇄
inductive Derivation {T N : Type} [DecidableEq T] [DecidableEq N]
    (G : Grammar T N) : List (GSymbol T N) → List (GSymbol T N) → Prop where
  | refl  : ∀ w, Derivation G w w                      -- 0번 적용 (자기 자신)
  | trans : ∀ w₁ w₂ w₃,
      DirectDerivation G w₁ w₂ → Derivation G w₂ w₃ →
      Derivation G w₁ w₃                                -- 1번 + 나머지

-- 문법이 생성하는 언어
def generatedLanguage {T N : Type} [DecidableEq T] [DecidableEq N]
    (G : Grammar T N) : List T → Prop :=
  fun w => Derivation G
    [GSymbol.nonterminal G.start]
    (w.map GSymbol.terminal)
```

---

## 4. 촘스키 위계 — 문법의 4가지 유형

### 4.1 왜 분류하는가?

모든 구-구조 문법이 같은 "힘"을 가지지 않는다. 규칙이 단순할수록 분석하기 쉽지만 표현할 수 있는 언어가 제한된다. 이런 관점에서 노엄 촘스키(Noam Chomsky)는 문법을 4가지 유형으로 분류했다.

### 4.2 촘스키 위계 (Chomsky Hierarchy)

| 유형 | 이름 | 생성 규칙의 제약 | 인식 기계 |
|------|------|-----------------|----------|
| **유형 0** | **비제한 문법**(unrestricted) | 제약 없음 | 튜링 기계 |
| **유형 1** | **문맥의존 문법**(context-sensitive) | lAr → lwr (A ∈ N, w ≠ λ) | 선형 유계 오토마톤 |
| **유형 2** | **문맥자유 문법**(context-free) | A → w (A ∈ N) | 푸시다운 오토마톤 |
| **유형 3** | **정규 문법**(regular) | A → aB 또는 A → a (A,B ∈ N, a ∈ T) | 유한상태 오토마톤 |

계층 관계: **유형 3 ⊂ 유형 2 ⊂ 유형 1 ⊂ 유형 0**

> 💡 마트료시카 인형을 떠올리면 된다: 가장 작은 인형(유형 3)이 그 다음 인형(유형 2) 안에 들어가고, 그것이 또 다음 인형(유형 1) 안에 들어간다.

### 4.3 각 유형의 상세 설명

#### 유형 3: **정규 문법**(Regular Grammar) — 가장 단순

생성 규칙이 다음 형태만 허용:
- A → aB (비단말 → 단말 + 비단말)
- A → a (비단말 → 단말)
- S → λ (시작 기호 → 공 문자열, S가 다른 규칙의 오른쪽에 안 나올 때만)

**예:** V = {S, A, 0, 1}, T = {0, 1}
- P = {S → 0S, S → 1A, S → 1, A → 1A, A → 1, S → λ}

이 문법은 {0ᵐ1ⁿ | m, n ≥ 0}을 생성한다 (예제 6의 G₂).

> 💡 정규 문법의 핵심: **하나의 비단말**이 **하나의 단말** + **하나의 비단말**로 바뀐다. 마치 일렬로 서서 한 명씩 지나가는 것과 같다. 이것이 유한상태 기계(Part 15-B, C에서 배움)와 정확히 대응한다.

```lean
-- 정규 문법의 생성 규칙 (유형 3)
inductive RegularProduction (T N : Type) where
  | toTermNonterm : N → T → N → RegularProduction T N  -- A → aB
  | toTerm        : N → T → RegularProduction T N       -- A → a
  | toEmpty       : N → RegularProduction T N            -- S → λ
```

#### 유형 2: **문맥자유 문법**(Context-Free Grammar, CFG) — 프로그래밍 언어의 기초

생성 규칙: **A → w** (왼쪽이 **정확히 하나의 비단말**)

유형 3보다 강력: 오른쪽(w)에 어떤 문자열이든 올 수 있다.

**예:** {0ⁿ1ⁿ | n ≥ 0}
- P = {S → 0S1, S → λ}
- S → 0S1에서 왼쪽은 S 하나뿐 → 유형 2 ✅
- S → λ에서 왼쪽은 S 하나뿐 → 유형 2 ✅

하지만 유형 3은 **아니다**: 오른쪽이 0S1 형태(단말-비단말-단말)인데, 유형 3에서는 aB(단말-비단말) 형태만 허용된다.

> 💡 **문맥자유**란?: 비단말 A가 나타나면 **주변 문맥에 관계없이** 항상 같은 규칙으로 치환할 수 있다는 뜻이다. 즉, A의 왼쪽이나 오른쪽에 무엇이 있든 상관없다.

```lean
-- 문맥자유 문법의 생성 규칙 (유형 2)
structure CFProduction (T N : Type) where
  lhs : N                          -- 왼쪽: 비단말 하나
  rhs : List (GSymbol T N)          -- 오른쪽: 아무 문자열
```

#### 유형 1: **문맥의존 문법**(Context-Sensitive Grammar)

생성 규칙: **lAr → lwr** (A ∈ N, l과 r은 문맥, w ≠ λ)

A를 w로 바꾸되, **A의 주변 문맥** l과 r이 맞아야만 치환할 수 있다.

**예:** {0ⁿ1ⁿ2ⁿ | n ≥ 0}은 문맥의존 문법으로 생성할 수 있지만, 문맥자유 문법으로는 불가능하다!

> 💡 **문맥의존**이란?: "A를 w로 바꾸려면 A 앞에 l이 있고 뒤에 r이 있어야 한다"는 제약이 있다. 즉, A를 **바꿀 수 있는 조건**이 문맥(주변)에 따라 달라진다.

#### 유형 0: **비제한 문법**(Unrestricted Grammar)

생성 규칙에 **제약이 없다**. 가장 강력하지만, 분석하기도 가장 어렵다.

### 4.4 유형 판별 방법 (연습문제 19 유형)

문법의 유형을 판별하려면 **모든 생성 규칙**을 확인해야 한다:

```
1. 모든 규칙이 A → aB 또는 A → a 형태? → 유형 3
2. 아니면, 모든 규칙의 왼쪽이 비단말 하나? → 유형 2
3. 아니면, 모든 규칙이 lAr → lwr 형태? → 유형 1
4. 아니면 → 유형 0
```

**예시 판별** (Rosen 연습문제 19 변형):

| 생성 규칙 | 판별 | 이유 |
|-----------|------|------|
| S → aA, A → a, A → b | 유형 3 | 모두 X → aY 또는 X → a 형태 |
| S → aAB, A → Bb, B → λ | 유형 0 (유형 1 아님) | B → λ가 비축소 규칙 위반 |
| S → ABa, AB → a | 유형 0 (유형 2 아님) | 왼쪽에 AB (비단말 2개) |
| S → bA, A → b, S → λ | 유형 3 | 모두 허용 형태 |

### 4.5 Lean 4에서 촘스키 유형 판별

```lean
-- 문법의 유형을 판별하는 함수 (간략화된 버전)
-- 실제로는 각 생성규칙의 형태를 검사해야 한다

/-- 유형 3 (정규) 생성인가? -/
def isRegularProd (p : Production T N) : Bool :=
  match p.lhs, p.rhs with
  | [.nonterminal _], [.terminal _] => true                  -- A → a
  | [.nonterminal _], [.terminal _, .nonterminal _] => true   -- A → aB
  | [.nonterminal _], [] => true                              -- S → λ
  | _, _ => false

/-- 유형 2 (문맥자유) 생성인가? -/
def isCFProd (p : Production T N) : Bool :=
  match p.lhs with
  | [.nonterminal _] => true   -- 왼쪽이 비단말 하나
  | _ => false
```

---

## 5. BNF 형식 — 프로그래밍 언어의 문법 표기법

### 5.1 BNF란?

**BNF**(Backus-Naur Form)는 문맥자유 문법(유형 2)을 표기하는 간결한 방법이다. 존 배커스(John Backus)와 페테르 나우르(Peter Naur)가 프로그래밍 언어 ALGOL 60의 구문을 기술하기 위해 개발했다.

BNF의 핵심 규칙:
- **→** 대신 **::=** 사용
- 비단말 기호를 **< >** 안에 넣는다
- 같은 비단말에 대한 여러 규칙을 **|** 로 구분하여 한 줄에 쓴다

### 5.2 BNF 예제

#### 영어 문장 문법의 BNF (Rosen 예제 14)

```
<sentence>     ::= <noun phrase><verb phrase>
<noun phrase>  ::= <article><adjective><noun> | <article><noun>
<verb phrase>  ::= <verb><adverb> | <verb>
<article>      ::= a | the
<adjective>    ::= large | hungry
<noun>         ::= rabbit | mathematician
<verb>         ::= eats | hops
<adverb>       ::= quickly | wildly
```

#### 부호 정수의 BNF (Rosen 예제 15)

```
<signed integer> ::= <sign><integer>
<sign>           ::= + | -
<integer>        ::= <digit> | <digit><integer>
<digit>          ::= 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9
```

이 문법으로 **-109**를 유도하면:
```
<signed integer>
→ <sign><integer>
→ -<integer>
→ -<digit><integer>
→ -1<integer>
→ -1<digit><integer>
→ -10<integer>
→ -10<digit>
→ -109 ✅
```

#### 프로그래밍 언어 식별자의 BNF (Rosen 예제 13)

```
<identifier> ::= <letter> | <identifier><letter> | <identifier><digit>
<letter>     ::= a | b | ... | z
<digit>      ::= 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9
```

이 규칙에 의하면: `x99a`는 유효한 식별자이고, `99x`는 유효하지 않다 (숫자로 시작하므로).

### 5.3 Lean 4에서 BNF 모델링

BNF는 본질적으로 문맥자유 문법이므로, Lean 4에서는 `CFProduction`으로 모델링할 수 있다:

```lean
-- 간단한 식별자 문법을 Lean 4로 모델링
inductive IdToken where
  | letter : Char → IdToken    -- 소문자
  | digit  : Nat → IdToken     -- 숫자 0~9

-- 식별자인지 검사하는 함수
def isValidIdentifier (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs =>
    c.isAlpha && cs.all (fun c => c.isAlpha || c.isDigit)

-- 테스트
#eval isValidIdentifier "x99a"   -- true
#eval isValidIdentifier "99x"    -- false
#eval isValidIdentifier ""       -- false
#eval isValidIdentifier "hello"  -- true
```

---

## 6. 유도 트리 — 유도 과정의 시각화

### 6.1 유도 트리란?

**유도 트리**(derivation tree) 또는 **구문분석 트리**(parse tree)는 문맥자유 문법에서의 유도 과정을 **트리**로 시각화한 것이다.

규칙:
- **루트**(root) = 시작 기호 S
- **내부 노드**(internal node) = 비단말 기호
- **잎**(leaf) = 단말 기호
- 부모 → 자식 관계 = 생성 규칙의 적용

### 6.2 예시: "the hungry rabbit eats quickly"의 유도 트리

```
              문장(sentence)
             /              \
      명사구(NP)          동사구(VP)
      /    |    \          /        \
  관사  형용사  명사     동사      부사
  (Art)  (Adj)  (N)     (V)      (Adv)
   |      |      |       |         |
  the  hungry  rabbit   eats    quickly
```

### 6.3 Lean 4로 유도 트리 표현

```lean
-- 유도 트리의 귀납적 정의
inductive ParseTree (T N : Type) where
  | leaf     : T → ParseTree T N                           -- 잎: 단말 기호
  | node     : N → List (ParseTree T N) → ParseTree T N    -- 내부: 비단말 + 자식들
  | emptyLeaf : ParseTree T N                               -- λ를 위한 빈 잎

-- 트리에서 단말 문자열 추출 (잎을 왼쪽→오른쪽으로 읽기)
def ParseTree.yield : ParseTree T N → List T
  | .leaf t      => [t]
  | .node _ cs   => cs.bind ParseTree.yield
  | .emptyLeaf   => []
```

---

## 7. 문자열 연결과 클레이니 스타

### 7.1 문자열 연결(Concatenation)

두 문자열 w₁과 w₂를 이어 붙이는 연산이다. 예: "ab" · "cd" = "abcd"

```lean
-- 문자열 연결은 리스트의 ++ 연산과 같다
#eval [0, 1] ++ [1, 0]   -- [0, 1, 1, 0]
```

### 7.2 집합의 연결

두 언어(문자열 집합) A, B의 **연결**(concatenation) AB는:

AB = {w₁w₂ | w₁ ∈ A, w₂ ∈ B}

**예:** A = {0, 11}, B = {1, 10}이면
- AB = {01, 010, 111, 1110}

### 7.3 Aⁿ과 A*

| 표기 | 의미 | 예 (A = {1, 00}) |
|------|------|------------------|
| A⁰ | {λ} | {λ} |
| A¹ | A | {1, 00} |
| A² | AA | {11, 100, 001, 0000} |
| A* | A⁰ ∪ A¹ ∪ A² ∪ ... | {λ, 1, 00, 11, 100, ...} |

**A*** 를 **클레이니 스타**(Kleene star) 또는 **클레이니 폐쇄**(Kleene closure)라 부른다.

```lean
-- 클레이니 스타의 귀납적 정의
inductive KleeneStar (A : List α → Prop) : List α → Prop where
  | empty : KleeneStar A []
  | concat : ∀ w₁ w₂, A w₁ → KleeneStar A w₂ → KleeneStar A (w₁ ++ w₂)
```

---

## 8. 연습문제

### 연습 8.1: 언어 생성 확인 [괄호 채우기]

다음 문법 G에서 L(G)를 구하라.

V = {S, A, a, b}, T = {a, b}, P = {S → aA, S → b, A → aa}

```lean
-- 아래 ⬜를 채워라
-- L(G)의 원소를 나열하는 함수
def L_G : List (List Char) :=
  [⬜, ⬜]  -- 힌트: 두 개의 단어

-- 검증
#eval L_G  -- 예상 출력: [['b'], ['a', 'a', 'a']]
```

<details>
<summary>📝 답 보기</summary>

```lean
def L_G : List (List Char) :=
  [['b'], ['a', 'a', 'a']]
-- S → b 로 "b" 생성
-- S → aA → a(aa) = "aaa" 생성
-- 더 이상의 유도 불가능
```

</details>

---

### 연습 8.2: 문법 설계 [skeleton]

집합 {0ⁿ1ⁿ | n ≥ 0}을 생성하는 문법의 생성 규칙을 완성하라.

```lean
-- 문법을 나타내는 구조체
-- V = {S, 0, 1}, T = {0, 1}
-- 생성 규칙을 완성하라

inductive Sym01 where | s0 | s1 | S
  deriving DecidableEq, Repr

-- P의 첫 번째 규칙: S → ⬜ S ⬜
-- P의 두 번째 규칙: S → ⬜
def productions_0n1n : List (List Sym01 × List Sym01) :=
  [ ([Sym01.S], [⬜, Sym01.S, ⬜]),   -- S → 0S1
    ([Sym01.S], ⬜) ]                  -- S → λ
```

<details>
<summary>📝 답 보기</summary>

```lean
def productions_0n1n : List (List Sym01 × List Sym01) :=
  [ ([Sym01.S], [Sym01.s0, Sym01.S, Sym01.s1]),  -- S → 0S1
    ([Sym01.S], []) ]                               -- S → λ
```

</details>

---

### 연습 8.3: 유도 과정 추적 [괄호 채우기]

다음 문법으로 "110"을 유도하는 과정을 완성하라.

V = {S, 0, 1}, T = {0, 1}, P = {S → 11S, S → 0}

```
S
⇒ ⬜         (규칙: S → ⬜ 사용)
⇒ ⬜         (규칙: S → ⬜ 사용)
```

<details>
<summary>📝 답 보기</summary>

```
S
⇒ 11S        (규칙: S → 11S 사용)
⇒ 110        (규칙: S → 0 사용)
```

</details>

---

### 연습 8.4: 문법이 생성하는 언어 [sorry]

다음 문법이 생성하는 언어를 구하고, Lean 4로 그 사실을 표현하라.

V = {S, 0, 1, A}, T = {0, 1}, P = {S → 1S, S → 00A, A → 0A, A → 0}

```lean
-- 이 문법이 생성하는 언어를 서술하라
-- 힌트: S → 1S를 k번 적용하면 1ᵏS가 된다
--       S → 00A를 적용하면 1ᵏ00A가 된다
--       A → 0A를 m번, A → 0을 1번 적용하면 1ᵏ00...0 (0이 m+3개)

-- L(G) = {1ᵏ0ⁿ | k ≥ 0, n ≥ 3}

-- Lean 4로 언어 표현
def L_ex4 (w : List Bool) : Prop :=
  sorry -- 1이 0개 이상 나온 후 0이 3개 이상 나오는 문자열
```

<details>
<summary>📝 답 보기</summary>

```lean
-- L(G) = {1ᵏ0ⁿ | k ≥ 0, n ≥ 3}
-- 1이 k개 나온 후 0이 n개(n ≥ 3) 나오는 비트열

def L_ex4 (w : List Bool) : Prop :=
  ∃ k n : Nat, n ≥ 3 ∧
    w = List.replicate k true ++ List.replicate n false
```

유도 예시 (111000):
- S → 1S → 11S → 111S → 11100A → 111000

</details>

---

### 연습 8.5: 촘스키 유형 판별 [괄호 채우기]

다음 생성 규칙의 문법이 유형 몇인지 판별하라.

```lean
-- (a) S → aA, A → a, A → b
-- 유형: ⬜ (0, 1, 2, 3 중)
-- 이유: ⬜

-- (b) S → ABa, AB → a
-- 유형: ⬜
-- 이유: ⬜

-- (c) S → bA, A → b, S → λ
-- 유형: ⬜
-- 이유: ⬜
```

<details>
<summary>📝 답 보기</summary>

```
(a) 유형: 3 (정규 문법)
이유: S → aA (비단말 → 단말 비단말), A → a (비단말 → 단말),
     A → b (비단말 → 단말) — 모두 유형 3 형태

(b) 유형: 0 (비제한 문법)
이유: AB → a에서 왼쪽이 비단말 2개(AB)이므로 유형 2(문맥자유)가 아님
     또한 문맥의존(유형 1)의 형태 lAr → lwr에도 맞지 않음
     (왼쪽 AB가 오른쪽 a로 줄어듦 → 비축소 조건 위반)

(c) 유형: 3 (정규 문법)
이유: S → bA (비단말 → 단말 비단말), A → b (비단말 → 단말),
     S → λ (시작 기호 → 공 문자열) — 모두 유형 3에서 허용
```

</details>

---

### 연습 8.6: 문법 설계 도전 [sorry]

다음 각 언어를 생성하는 구-구조 문법의 생성 규칙을 설계하라.

```lean
-- (a) {1ⁿ | n ≥ 0} = {λ, 1, 11, 111, ...}
-- P = { S → ⬜, S → ⬜ }

-- (b) 0으로 시작하고 1로 끝나는 비트열의 집합
-- P = { sorry }

-- (c) {0ⁿ1²ⁿ | n ≥ 0} = {λ, 011, 001111, ...}
-- P = { sorry }
```

<details>
<summary>📝 답 보기</summary>

```
(a) {1ⁿ | n ≥ 0}
P = { S → 1S, S → λ }
검증: S → λ (n=0), S → 1S → 1λ = 1 (n=1), S → 1S → 11S → 11λ = 11 (n=2), ...

(b) 0으로 시작하고 1로 끝나는 비트열
P = { S → 0A1, A → 0A, A → 1A, A → λ }
설명: S → 0A1에서 0과 1 사이에 A를 넣고,
A는 0이나 1을 자유롭게 추가하거나 λ로 종료
검증: S → 0A1 → 01 (최단), S → 0A1 → 00A1 → 001, ...

(c) {0ⁿ1²ⁿ | n ≥ 0}
P = { S → 0S11, S → λ }
검증: S → λ (n=0), S → 0S11 → 0λ11 = 011 (n=1),
S → 0S11 → 00S1111 → 00λ1111 = 001111 (n=2), ...
핵심: S → 0S11은 0을 1개 추가할 때마다 1을 2개 추가한다!
```

</details>

---

### 연습 8.7: BNF 형식 [괄호 채우기]

다음 영어 문법의 BNF 형식을 완성하라.

```
<sentence>     ::= <noun phrase>⬜
<noun phrase>  ::= <article>⬜<noun> | <article><noun>
<verb phrase>  ::= ⬜<adverb> | <verb>
<article>      ::= ⬜ | ⬜
<noun>         ::= rabbit | ⬜
<verb>         ::= ⬜ | hops
<adverb>       ::= quickly | ⬜
```

<details>
<summary>📝 답 보기</summary>

```
<sentence>     ::= <noun phrase><verb phrase>
<noun phrase>  ::= <article><adjective><noun> | <article><noun>
<verb phrase>  ::= <verb><adverb> | <verb>
<article>      ::= a | the
<noun>         ::= rabbit | mathematician
<verb>         ::= eats | hops
<adverb>       ::= quickly | wildly
```

</details>

---

### 연습 8.8: 식별자 유효성 검사 [sorry]

Lean 4로 "문자로 시작하고 문자 또는 숫자로 구성된 식별자"를 검사하는 함수를 완성하라.

```lean
-- 식별자가 유효한지 검사
-- 규칙: 소문자로 시작, 이후 소문자 또는 숫자
def isValidId (s : String) : Bool :=
  sorry

-- 테스트
#eval isValidId "abc"    -- true
#eval isValidId "x99a"   -- true
#eval isValidId "99x"    -- false
#eval isValidId ""       -- false
#eval isValidId "a"      -- true
```

<details>
<summary>📝 답 보기</summary>

```lean
def isValidId (s : String) : Bool :=
  match s.toList with
  | [] => false                              -- 빈 문자열 → 무효
  | c :: cs =>
    c.isAlpha &&                             -- 첫 글자는 반드시 문자
    cs.all (fun ch => ch.isAlpha || ch.isDigit)  -- 나머지는 문자 또는 숫자
```

</details>

---

### 연습 8.9: 종합 도전 — 문법에서 언어, 언어에서 문법 [sorry]

**(a)** 다음 문법이 생성하는 언어를 기술하라:

V = {S, A, B, a, b}, T = {a, b}
P = {S → AB, S → aA, A → a, B → ba}

```lean
-- L(G)를 기술하라:
-- S → AB → ⬜ → ⬜  (첫 번째 경로)
-- S → aA → ⬜       (두 번째 경로)
-- 따라서 L(G) = { sorry }
```

**(b)** 다음 언어를 생성하는 문법을 설계하라:

L = {aⁿbⁿ | n ≥ 1} (공 문자열 미포함)

```lean
-- V = ⬜, T = {a, b}, S는 시작 기호
-- P = { sorry }
```

<details>
<summary>📝 답 보기</summary>

```
(a) L(G) = {aba, aa}
경로 1: S → AB → aB → a(ba) = aba
경로 2: S → aA → a(a) = aa
(A → a는 a 하나만 생성, B → ba는 ba만 생성)

(b) L = {aⁿbⁿ | n ≥ 1}
V = {S, a, b}, T = {a, b}
P = { S → aSb, S → ab }

검증:
- n=1: S → ab ✅
- n=2: S → aSb → a(ab)b = aabb ✅
- n=3: S → aSb → a(aSb)b → a(a(ab)b)b = aaabbb ✅

핵심: S → ab가 기저 사례(base case)이고,
S → aSb가 재귀 단계(recursive step)이다.
{0ⁿ1ⁿ}과 같은 패턴이지만 λ를 제외하기 위해 S → λ 대신 S → ab를 사용한다.
```

</details>

---

## 9. 핵심 요약

| 개념 | 정의 | Lean 4 표현 |
|------|------|------------|
| **어휘**(vocabulary) V | 기호의 유한집합 | `inductive Symbol` |
| **단어**(word) | V의 원소로 된 유한 문자열 | `List Symbol` |
| **공 문자열**(empty string) λ | 길이 0인 문자열 | `[]` |
| **V*** | V에서 만들 수 있는 모든 단어의 집합 | `List Symbol → Prop` |
| **언어**(language) L | V*의 부분집합 | `List Symbol → Prop` |
| **구-구조 문법** G | (V, T, S, P) | `Grammar T N` |
| **단말**(terminal) | 최종 기호 | `GSymbol.terminal` |
| **비단말**(nonterminal) | 치환 가능한 기호 | `GSymbol.nonterminal` |
| **생성**(production) | w₀ → w₁ | `Production T N` |
| **유도**(derivation) | S ⇒* w | `Derivation G` |
| **유형 3** (정규) | A → aB \| a | 유한상태 오토마톤 |
| **유형 2** (문맥자유) | A → w | 프로그래밍 언어 구문 |
| **유형 1** (문맥의존) | lAr → lwr | 더 강력한 언어 |
| **유형 0** (비제한) | 제약 없음 | 튜링 기계 |
| **BNF** | 유형 2의 간결한 표기 | ::=, \|, < > 사용 |
| **유도 트리** | 유도 과정의 트리 표현 | `ParseTree T N` |

---

## 다음 파트 예고

**Part 15-B**에서는:
- **출력이 있는 유한상태 기계**(Mealy machine, Moore machine) — 자동판매기, 이진 덧셈기 모델
- **전이함수**(transition function)와 **출력함수**(output function)
- **상태도**(state diagram)와 **상태표**(state table)
- Lean 4로 유한상태 기계를 모델링하고 시뮬레이션하는 방법
