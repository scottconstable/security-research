/*
 * Copyright (C) Intel Corporation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/*
 * File name: PCIe_IDE_transaction_ordering.als
 * Description: Models PCIe IDE integrity and transaction ordering behavior.
 */

/**
 * Use a small threshold to keep the analysis tractable.
 */
fun Counter_Threshold : Int { 3 }

abstract sig MessageQueues {}
one sig NextSendMessage extends MessageQueues {}
one sig NextRecvMessage extends MessageQueues {}
one sig FirstSendMessage, FirstRecvMessage in Message {}

/**
 * The class of stateful objects that may have counter values
 */
abstract sig A_CntObj {
	var Counter_NPR : lone Int,
	var Counter_CPL : lone Int
}
one sig PR_Sent, PR_Received extends A_CntObj {}
abstract sig Message extends A_CntObj {
	send_order : lone Message,
	recv_order : lone Message,
	var Queue : set MessageQueues
} {
	// These constraints simplify the model checking, but they also preclude
	// modeling replay attacks. While it is possible to model replay attacks,
	// this adds a lot of complexity to the model and slows model checking.
	this not in this.^@send_order // The send order does not repeat messages
	Message in FirstSendMessage.*@send_order // One message must be first
	this not in this.^@recv_order // The repeat order does not repeat messages
	Message in FirstRecvMessage.*@recv_order // One message must be first
}
sig PR, NPR, CPL extends Message {}
sig IDE_Sync extends PR {}

abstract sig ErrorCode {}
one sig CounterError extends ErrorCode {}
one sig IntegrityError extends ErrorCode {}
var sig Error in ErrorCode {}

pred Send_PR[m : Message] {
	m in PR - IDE_Sync
	Counter_NPR' = Counter_NPR ++ PR_Sent -> plus[PR_Sent.Counter_NPR, 1]
	Counter_CPL' = Counter_CPL ++ PR_Sent -> plus[PR_Sent.Counter_CPL, 1]
}

pred Send_IDE_Sync[m : Message] {
	m in IDE_Sync
	let NewCounterNPR = plus[PR_Sent.Counter_NPR, 1],
		NewCounterCPL = plus[PR_Sent.Counter_CPL, 1]  {
		Counter_NPR' = Counter_NPR ++ (PR_Sent -> 0 + m -> NewCounterNPR)
		Counter_CPL' = Counter_CPL ++ (PR_Sent -> 0 + m -> NewCounterCPL)
	}
}

pred Send_NPR[m : Message] {
	m in NPR
	Counter_NPR' = Counter_NPR ++ (m -> PR_Sent.Counter_NPR + PR_Sent -> 0)
	Counter_CPL' = Counter_CPL
}

pred Send_CPL[m : Message] {
	m in CPL
	Counter_NPR' = Counter_NPR
	Counter_CPL' = Counter_CPL ++ (m -> PR_Sent.Counter_CPL + PR_Sent -> 0)
}

pred Recv_PR[m : Message] {
	m in PR - IDE_Sync
	Counter_NPR' = Counter_NPR ++ PR_Received -> plus[PR_Received.Counter_NPR, 1]
	Counter_CPL' = Counter_CPL ++ PR_Received -> plus[PR_Received.Counter_CPL, 1]
	CounterError not in Error'
}

pred Recv_IDE_Sync[m : Message] {
	m in IDE_Sync
	let New_Counter_NPR = minus[plus[PR_Received.Counter_NPR, 1], m.Counter_NPR],
		New_Counter_CPL = minus[plus[PR_Received.Counter_CPL, 1], m.Counter_CPL] {
		Counter_NPR' = Counter_NPR ++ PR_Received -> New_Counter_NPR
		Counter_CPL' = Counter_CPL ++ PR_Received -> New_Counter_CPL
		(New_Counter_NPR < 0 or New_Counter_CPL < 0) implies
			CounterError in Error' else CounterError not in Error'
	}
}

pred Recv_NPR[m : Message] {
	m in NPR
	let New_Counter_NPR = minus[PR_Received.Counter_NPR, m.Counter_NPR] {
		Counter_NPR' = Counter_NPR ++ PR_Received -> New_Counter_NPR
		Counter_CPL' = Counter_CPL
		(New_Counter_NPR < 0) implies CounterError in Error' else CounterError not in Error'
	}
}

pred Recv_CPL[m : Message] {
	m in CPL
	let New_Counter_CPL = minus[PR_Received.Counter_CPL, m.Counter_CPL] {
		Counter_NPR' = Counter_NPR
		Counter_CPL' = Counter_CPL ++ PR_Received -> New_Counter_CPL
		(New_Counter_CPL < 0) implies CounterError in Error' else CounterError not in Error'
	}
}

/**
 * True iff m has been sent by the transmitter
 */
pred Sent[m : Message] {	let M = ~Queue[NextSendMessage] | no M or M in m.^send_order }

/**
 * True iff m has been received by the receiver
 */
pred Received[m : Message] { let M = ~Queue[NextRecvMessage] | no M or M in m.^recv_order }

pred Send[m : Message] {
	m = ~Queue[NextSendMessage]
	~Queue'[NextSendMessage] = m.send_order
	~Queue'[NextRecvMessage] = ~Queue[NextRecvMessage]
	no Error'
	(PR_Sent.Counter_NPR >= Counter_Threshold or
	 PR_Sent.Counter_CPL >= Counter_Threshold) implies {
		Send_IDE_Sync[m]
	} else {
		Send_PR[m] or Send_NPR[m] or Send_CPL[m] or Send_IDE_Sync[m]
	}
}

pred Recv[m : Message] {
	m = ~Queue[NextRecvMessage]
	Sent[m]
	~Queue'[NextRecvMessage] = m.recv_order
	~Queue'[NextSendMessage] = ~Queue[NextSendMessage]
	Recv_PR[m] or Recv_NPR[m] or Recv_CPL[m] or Recv_IDE_Sync[m]

	// This abstraction detects reordering within each substream.
	(some mm : Message | m in mm.^send_order and not Received[mm] and
						 (m + mm in PR or m + mm in NPR or m + mm in CPL))
		iff IntegrityError in Error'
}

// Alloy's current implementation of temporal logic requires a stutter to allow
// the state sequence to loop back on itself. A future implementation might lift
// this requirement, in which case the stutter can be removed from the model.
pred Stutter {
	Counter_NPR' = Counter_NPR
	Counter_CPL' = Counter_CPL
	Queue' = Queue
	Error' = Error
}

fact Init {
	all o : A_CntObj - Message | o.Counter_NPR = 0 and o.Counter_CPL = 0
	all m : Message | no m.Counter_NPR and no m.Counter_CPL
	~Queue[NextSendMessage] = FirstSendMessage
	~Queue[NextRecvMessage] = FirstRecvMessage
	no Error
}

/**
 * Think of this as the main loop that non-deterministically selects a message
 * to send or receive (a message can only be received if it has been sent)
 */
fact Behavior_Interleaved {
	always (no Error and some ~Queue[NextRecvMessage]
		implies (some m : Message | Send[m] or Recv[m])
		else Stutter)
}

/**
 * This is an alternative loop that also non-deterministically selects
 * messages to send and receive, but with the added constraint that all
 * messages must be sent before any can be received. For security and
 * correctness assertions, this sequential behavior is adequate and can
 * be run much faster by the SAT solvers.
 */
/*fact Behavior_Sequential {
	always (no Error and some ~Queue[NextRecvMessage]
		implies (some m : Message | Send[m] or (no ~Queue[NextSendMessage] and Recv[m]))
		else Stutter)
}*/

/**
 * Some examples that showcase benign and malicious traces
 */
run Example1 { eventually (IntegrityError in Error) } for 5 Message, 5 steps
run Example2 {
	~Queue[NextSendMessage] in PR - IDE_Sync
	~Queue[NextSendMessage].send_order in IDE_Sync
	~Queue[NextSendMessage].send_order.send_order in CPL
	~Queue[NextSendMessage].send_order.send_order.send_order in NPR
	always no Error
} for exactly 4 Message, exactly 9 steps
run Example3 {
	always no Error and eventually (PR_Received.Counter_CPL = 4)
} for exactly 6 Message, exactly 13 steps

pred Integrity_Holds_At_State {
	all m1, m2 : Message | (m1 + m2 in PR or m1 + m2 in NPR or m1 + m2 in CPL) and
		Received[m2] and m2 in m1.^send_order => Received[m1]
}

/**
 * Assert that whenever TLPs within a substream are re-ordered, an Integrity
 * Error will be signaled immediately. Conversely, this also asserts that an
 * Integrity Error will only be signaled when an integrity violation occurs
 * (i.e., the protocol cannot signal spurious integrity errors)
 */
assert Integrity_Iff_No_Integrity_Error {
	always (Integrity_Holds_At_State <=> IntegrityError not in Error)
}
check Integrity_Iff_No_Integrity_Error for 5 Message, 11 steps

pred Ordering_Permitted {
	all m1, m2 : Message | (m2 in m1.^send_order and m1 in m2.^recv_order) implies
		((m1 in NPR and m2 in CPL) or (m1 in CPL and m2 in NPR) or (m2 in PR and m1 not in PR))
}

pred Ordering_Permitted_At_State {
	all m1, m2 : Message | m2 in m1.^send_order and Received[m2] and
		(m1 + m2 in NPR or m1 + m2 in CPL or m1 in PR) implies Received[m1]
}

check {
	Ordering_Permitted iff always Ordering_Permitted_At_State
} for exactly 4 Message, exactly 9 steps

/**
 * Assert that the model permits an ordering if and only if it has not
 * signaled an error.
 *
 * This assertion does not hold for the baseline model. It can fail even if only
 * two messages are reordered, including an IDE_Sync+CPL or IDE_Sync+NPR pair.
 */
assert Ordering_Permitted_No_Error {
	always (Ordering_Permitted_At_State <=> no Error)
}
check Ordering_Permitted_No_Error for 2 Message, 5 steps

/**
 * The baseline model does not eventually detect every ordering violation. This
 * assertion fails even for just two messages.
 */
assert Not_Ordering_Permitted_Implies_Eventually_Error {
	not Ordering_Permitted implies eventually some Error
}
check Not_Ordering_Permitted_Implies_Eventually_Error for exactly 2 Message, exactly 5 steps

/**
 * Assert that whenever intra-substream ordering holds but TLPs are otherwise
 * reordered in a prohibited fashion, the model immediately signals a counter
 * error.
 *
 * This assertion does not hold for the baseline model.
 */
assert Integrity_And_Not_Ordering_Permitted_Iff_Counter_Error {
	always ((Integrity_Holds_At_State and not Ordering_Permitted_At_State) <=>
				(IntegrityError not in Error and CounterError in Error))
}
check Integrity_And_Not_Ordering_Permitted_Iff_Counter_Error for 2 Message, 5 steps

/**
 * Assert that the receiver can receive all packets in a permitted ordering. In
 * other words, this assertion checks that the protocol does not prevent valid reorderings.
 */
assert Ordering_Permitted_Implies_All_TLPs_Received {
	Ordering_Permitted implies eventually no ~Queue[NextRecvMessage]
}
check Ordering_Permitted_Implies_All_TLPs_Received for exactly 4 Message, exactly 9 steps

assert Ordering_Permitted_Implies_No_Error {
	Ordering_Permitted implies always no Error
}
check Ordering_Permitted_Implies_No_Error for exactly 4 Message, exactly 9 steps

run ExampleReorder {
	always no Error
	some npr : NPR, pr : (PR - IDE_Sync) |
		npr in pr.^send_order and pr in npr.^recv_order
		and no (IDE_Sync & npr.^~send_order)
} for exactly 6 Message, exactly 13 steps

pred IsProhibitedReorder[npr_or_cpl : Message, pr : Message] {
	npr_or_cpl in NPR + CPL
	pr in PR
	npr_or_cpl in pr.^send_order
	pr in npr_or_cpl.^recv_order
}

/** The following predicates and assertions are intended to test the conditions
 *  under which a reordering violation is *silent*, meaning it is never detected
 *  by the receiver; versus the conditions under which a reordering violation is
 *  *noisy*, meaning it is eventually detected by the receiver. */

pred IsSilentReorder[npr_or_cpl : Message, pr : Message] {
	IsProhibitedReorder[npr_or_cpl, pr]
	some sync : IDE_Sync {
		npr_or_cpl in sync.^send_order
		sync in pr.*send_order
		no (PR & (sync.^send_order & npr_or_cpl.^~send_order))
		sync in npr_or_cpl.^recv_order
	}
}

assert SilentReorder {
	always IntegrityError not in Error implies
	(always CounterError not in Error iff
		all npr_or_cpl : NPR + CPL, pr : PR |
			IsProhibitedReorder[npr_or_cpl, pr] implies
				IsSilentReorder[npr_or_cpl, pr])
}
check SilentReorder for exactly 6 Message, exactly 13 steps

fun PRSentCounterNPRAfterSent(m : Message) : Int {
	m in NPR + IDE_Sync => 0 else
	let NPR_Reset = { mprev : (NPR + IDE_Sync) & m.^~send_order |
			no ((IDE_Sync + NPR) & mprev.^send_order & m.^~send_order) } {
		some NPR_Reset => #(PR & NPR_Reset.^send_order & m.*~send_order)
			else #(PR & m.*~send_order)
	}
}

fun PRSentCounterCPLAfterSent(m : Message) : Int {
	m in CPL + IDE_Sync => 0 else
	let CPL_Reset = { mprev : (CPL + IDE_Sync) & m.^~send_order |
			no ((IDE_Sync + CPL) & mprev.^send_order & m.^~send_order) } {
		some CPL_Reset => #(PR & CPL_Reset.^send_order & m.*~send_order)
			else #(PR & m.*~send_order)
	}
}

assert PRSentCounterAfterSentIsValid {
	always IntegrityError not in Error implies
	all m : Message |
		eventually Send[m] implies 
			eventually (Send[m]; (
				PR_Sent.Counter_NPR = PRSentCounterNPRAfterSent[m] and
				PR_Sent.Counter_CPL = PRSentCounterCPLAfterSent[m]
			))
}
check PRSentCounterAfterSentIsValid for exactly 5 Message, exactly 11 steps

pred IsNoisyReorder[npr_or_cpl : Message, pr : Message] {
	IsProhibitedReorder[npr_or_cpl, pr]
	some sync : IDE_Sync, X, Y : Int {
		npr_or_cpl in sync.^send_order
		some (PR & (sync.^send_order & npr_or_cpl.^~send_order))
		no (IDE_Sync & (sync.^send_order & npr_or_cpl.^~send_order))
		sync in npr_or_cpl.^recv_order
		npr_or_cpl in NPR => {
			PRSentCounterNPRAfterSent[npr_or_cpl.~send_order] = Y
			eventually (Recv[npr_or_cpl.~recv_order]; PR_Received.Counter_NPR = X)
		} else {
			PRSentCounterCPLAfterSent[npr_or_cpl.~send_order] = Y
			eventually (Recv[npr_or_cpl.~recv_order]; PR_Received.Counter_CPL = X)
		}
		X >= Y
	}
}

assert NoisyReorder {
	always IntegrityError not in Error implies
	all npr_or_cpl : NPR + CPL |
		eventually (Recv[npr_or_cpl]; CounterError not in Error) implies
			(all pr : PR | IsProhibitedReorder[npr_or_cpl, pr] iff
				(IsSilentReorder[npr_or_cpl, pr] or IsNoisyReorder[npr_or_cpl, pr]))
}
check NoisyReorder for exactly 5 Message, exactly 11 steps

assert NoisyReorderImpliesDelayedError {
	always IntegrityError not in Error implies
	all npr_or_cpl : NPR + CPL, pr : PR |
		IsNoisyReorder[npr_or_cpl, pr]	and eventually Recv[npr_or_cpl] implies
			eventually (Recv[npr_or_cpl]; CounterError not in Error)
}
check NoisyReorderImpliesDelayedError for exactly 5 Message, exactly 11 steps

assert NoisyReorderImpliesEventuallyError {
	always IntegrityError not in Error and
	(some npr_or_cpl : NPR + CPL, pr : PR | IsNoisyReorder[npr_or_cpl, pr])
	implies eventually CounterError in Error
}
check NoisyReorderImpliesEventuallyError for exactly 5 Message, exactly 11 steps

assert NoisyAndSilentAreMutuallyExclusive {
	all npr_or_cpl : NPR + CPL, pr : PR |
		not (IsSilentReorder[npr_or_cpl, pr] and IsNoisyReorder[npr_or_cpl, pr])
}
check NoisyAndSilentAreMutuallyExclusive for exactly 8 Message, exactly 17 steps

assert NoisyReorderAlwaysCaughtAtLatestByOldestBypassedIDESync {
	always IntegrityError not in Error implies
	all npr_or_cpl : NPR + CPL, pr : PR |
		IsNoisyReorder[npr_or_cpl, pr] and eventually Recv[npr_or_cpl] implies
		some sync : IDE_Sync & npr_or_cpl.^recv_order {
			no (IDE_Sync & npr_or_cpl.^recv_order & sync.^~recv_order)
			((not eventually Recv[sync]) or eventually (Recv[sync]; CounterError in Error))
		}
}
check NoisyReorderAlwaysCaughtAtLatestByOldestBypassedIDESync for exactly 7 Message, exactly 15 steps