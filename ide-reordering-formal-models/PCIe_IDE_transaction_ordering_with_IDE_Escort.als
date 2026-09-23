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
 * File name: PCIe_IDE_transaction_ordering_with_IDE_Escort.als
 * Description: Models the IDE Escort feature.
 */

fun Counter_Threshold : Int { 3 }

abstract sig MessageQueues {}
one sig NextSendMessage extends MessageQueues {}
one sig NextRecvMessage extends MessageQueues {}

abstract sig OverflowBits {}
one sig Overflow_NPR extends OverflowBits {}
one sig Overflow_CPL extends OverflowBits {}

/**
 * The class of objects that may have counter values
 */
abstract sig A_CntObj {
	var Counter_NPR : lone Int,
	var Counter_CPL : lone Int,
	var Overflow : set OverflowBits,
	var Queue : set MessageQueues
}
one sig PR_Sent, PR_Received, IDE_Sync_Received extends A_CntObj {}
abstract sig Message extends A_CntObj {
	send_order : lone Message,
	recv_order : lone Message
} {
	// These constraints simplify the model checking, but they also preclude
	// modeling replay attacks. While it is possible to model replay attacks,
	// this adds a lot of complexity to the model and slows model checking.
	this not in this.^@send_order // The send order does not repeat messages
	some m : Message | Message in m.*@send_order // One message must be first
	this not in this.^@recv_order // The repeat order does not repeat messages
	some m : Message | Message in m.*@recv_order // One message must be first
}
sig PR, NPR, CPL extends Message {}
sig IDE_Sync, IDE_Sync_NPR, IDE_Sync_CPL extends PR {}

abstract sig ErrorCode {}
one sig CounterError extends ErrorCode {}
one sig IntegrityError extends ErrorCode {}
var sig Error in ErrorCode {}

pred Send_PR[m : Message] {
	m in PR - (IDE_Sync_NPR + IDE_Sync_CPL + IDE_Sync)
	Counter_NPR' = Counter_NPR ++ PR_Sent -> plus[PR_Sent.Counter_NPR, 1]
	Counter_CPL' = Counter_CPL ++ PR_Sent -> plus[PR_Sent.Counter_CPL, 1]
	Overflow' = Overflow
}

pred Send_IDE_Sync_NPR[m : Message] {
	m in IDE_Sync_NPR
	Counter_NPR' = Counter_NPR ++ PR_Sent -> plus[PR_Sent.Counter_NPR, 1]
	Counter_CPL' = Counter_CPL ++ PR_Sent -> plus[PR_Sent.Counter_CPL, 1]
	Overflow' = Overflow
}

pred Send_IDE_Sync_CPL[m : Message] {
	m in IDE_Sync_CPL
	Counter_NPR' = Counter_NPR ++ PR_Sent -> plus[PR_Sent.Counter_NPR, 1]
	Counter_CPL' = Counter_CPL ++ PR_Sent -> plus[PR_Sent.Counter_CPL, 1]
	Overflow' = Overflow
}

pred Send_IDE_Sync[m : Message] {
	m in IDE_Sync
	let NewCounterNPR = plus[PR_Sent.Counter_NPR, 1],
		NewCounterCPL = plus[PR_Sent.Counter_CPL, 1]  {
		Counter_NPR' = Counter_NPR ++ (PR_Sent -> 0 + m -> NewCounterNPR)
		Counter_CPL' = Counter_CPL ++ (PR_Sent -> 0 + m -> NewCounterCPL)
	}
	Overflow' = Overflow ++ PR_Sent -> { Overflow_NPR + Overflow_CPL }
}

pred Send_NPR[m : Message] {
	m in NPR
	Counter_NPR' = Counter_NPR ++ (m -> PR_Sent.Counter_NPR + PR_Sent -> 0)
	Counter_CPL' = Counter_CPL
	Overflow' = Overflow ++ (
		m -> (PR_Sent.Overflow & Overflow_NPR) +
		PR_Sent -> (Overflow[PR_Sent] - Overflow_NPR))
}

pred Send_CPL[m : Message] {
	m in CPL
	Counter_NPR' = Counter_NPR
	Counter_CPL' = Counter_CPL ++ (m -> PR_Sent.Counter_CPL + PR_Sent -> 0)
	Overflow' = Overflow ++ (
		m -> (PR_Sent.Overflow & Overflow_CPL) +
		PR_Sent -> (Overflow[PR_Sent] - Overflow_CPL))
}

pred Recv_PR[m : Message] {
	m in PR - (IDE_Sync_NPR + IDE_Sync_CPL + IDE_Sync)
	Counter_NPR' = Counter_NPR ++ PR_Received -> plus[PR_Received.Counter_NPR, 1]
	Counter_CPL' = Counter_CPL ++ PR_Received -> plus[PR_Received.Counter_CPL, 1]
	CounterError not in Error'
}

pred Recv_IDE_Sync_NPR[m : Message] {
	m in IDE_Sync_NPR
	Counter_NPR' = Counter_NPR ++ (
		PR_Received -> plus[PR_Received.Counter_NPR, 1] +
		IDE_Sync_Received -> plus[IDE_Sync_Received.Counter_NPR, 1])
	Counter_CPL' = Counter_CPL ++ PR_Received -> plus[PR_Received.Counter_CPL, 1]
	CounterError not in Error'
}

pred Recv_IDE_Sync_CPL[m : Message] {
	m in IDE_Sync_CPL
	Counter_NPR' = Counter_NPR ++ PR_Received -> plus[PR_Received.Counter_NPR, 1]
	Counter_CPL' = Counter_CPL ++ (
		PR_Received -> plus[PR_Received.Counter_CPL, 1] +
		IDE_Sync_Received -> plus[IDE_Sync_Received.Counter_CPL, 1])
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
	let New_Counter_NPR = minus[PR_Received.Counter_NPR, m.Counter_NPR],
		New_IDE_Sync_Counter_NPR = (Overflow_NPR in m.Overflow =>
			minus[IDE_Sync_Received.Counter_NPR, 1] else IDE_Sync_Received.Counter_NPR) {
		(New_Counter_NPR < 0 or New_IDE_Sync_Counter_NPR = -1) implies { // Underflow case
			Counter_NPR' = Counter_NPR
			CounterError in Error'
		} else {
			Counter_NPR' = Counter_NPR ++ (
				PR_Received -> New_Counter_NPR +
				IDE_Sync_Received -> New_IDE_Sync_Counter_NPR)
			CounterError not in Error'
		}
	}
	Counter_CPL' = Counter_CPL
}

pred Recv_CPL[m : Message] {
	m in CPL
	let New_Counter_CPL = minus[PR_Received.Counter_CPL, m.Counter_CPL],
		New_IDE_Sync_Counter_CPL = (Overflow_CPL in m.Overflow =>
			minus[IDE_Sync_Received.Counter_CPL, 1] else IDE_Sync_Received.Counter_CPL) {
		(New_Counter_CPL < 0 or New_IDE_Sync_Counter_CPL = -1) implies { // Underflow case
			Counter_CPL' = Counter_CPL
			CounterError in Error'
		} else {
			Counter_CPL' = Counter_CPL ++ (
				PR_Received -> New_Counter_CPL +
				IDE_Sync_Received -> New_IDE_Sync_Counter_CPL)
			CounterError not in Error'
		}
	}
	Counter_NPR' = Counter_NPR
}

/**
 * True iff m has been sent by the transmitter
 */
pred Sent[m : Message] {	let M = ~Queue[NextSendMessage] | no M or m in M.^~send_order }

/**
 * True iff m has been received by the receiver
 */
pred Received[m : Message] { let M = ~Queue[NextRecvMessage] | no M or m in M.^~recv_order }

pred Send[m : Message] {
	m = ~Queue[NextSendMessage]
	~Queue'[NextSendMessage] = m.send_order
	~Queue'[NextRecvMessage] = ~Queue[NextRecvMessage]
	no Error'
	(some m.~send_order and m.~send_order in IDE_Sync_NPR) implies {
		Send_NPR[m]
	} else (some m.~send_order and m.~send_order in IDE_Sync_CPL) implies {
		Send_CPL[m]
	} else (PR_Sent.Counter_NPR >= Counter_Threshold or
			PR_Sent.Counter_CPL >= Counter_Threshold) implies {
		Send_IDE_Sync[m]
	} else {
		Send_PR[m] or Send_IDE_Sync[m] or
			(Send_IDE_Sync_NPR[m] and Overflow_NPR in PR_Sent.Overflow) or
			(Send_IDE_Sync_CPL[m] and Overflow_CPL in PR_Sent.Overflow) or
			(Send_NPR[m] and Overflow_NPR not in PR_Sent.Overflow) or
			(Send_CPL[m] and Overflow_CPL not in PR_Sent.Overflow)
	}
}

pred Recv[m : Message] {
	m = ~Queue[NextRecvMessage]
	Sent[m]
	~Queue'[NextRecvMessage] = m.recv_order
	~Queue'[NextSendMessage] = ~Queue[NextSendMessage]
	Overflow' = Overflow
	Recv_PR[m] or Recv_NPR[m] or Recv_CPL[m] or Recv_IDE_Sync[m] or
		Recv_IDE_Sync_NPR[m] or Recv_IDE_Sync_CPL[m]

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
	Overflow' = Overflow
	Queue' = Queue
	Error' = Error
}

fact Init {
	all o : A_CntObj - Message | o.Counter_NPR = 0 and o.Counter_CPL = 0
	all m : Message | no m.Counter_NPR and no m.Counter_CPL
	no Overflow
	~Queue[NextSendMessage] = { m : Message | no m.~send_order }
	~Queue[NextRecvMessage] = { m : Message | no m.~recv_order }
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
	~Queue[NextSendMessage] in PR - (IDE_Sync + IDE_Sync_NPR + IDE_Sync_CPL)
	~Queue[NextSendMessage].send_order in IDE_Sync
	~Queue[NextSendMessage].send_order.send_order in IDE_Sync_NPR
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

check { Ordering_Permitted iff always Ordering_Permitted_At_State } for exactly 4 Message, exactly 9 steps

/**
 * Assert that the model permits an ordering if and only if it has not
 * signaled an error.
 */
assert Ordering_Permitted_No_Error {
	always (Ordering_Permitted_At_State <=> no Error)
}
check Ordering_Permitted_No_Error for exactly 5 Message, exactly 11 steps

assert Integrity_And_Not_Ordering_Permitted_Iff_Counter_Error {
	always ((Integrity_Holds_At_State and not Ordering_Permitted_At_State) <=>
				(IntegrityError not in Error and CounterError in Error))
}
check Integrity_And_Not_Ordering_Permitted_Iff_Counter_Error for exactly 4 Message, exactly 9 steps

/**
 * Assert that the receiver can receive all packets in a permitted ordering. In
 * other words, this assertion checks that the protocol does not prevent valid reorderings.
 */
assert Ordering_Permitted_Implies_All_TLPs_Received {
	Ordering_Permitted implies eventually no ~Queue[NextRecvMessage]
}
check Ordering_Permitted_Implies_All_TLPs_Received for exactly 4 Message, exactly 9 steps