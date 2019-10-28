// =======================================
// ============== SIGNATURES =============
open util/ordering [Time] as T

// Time unit
sig Time {}

// WTP signature, core system containing the four subsystems
one sig WTP {
	console:  one  Console,
	sensor:   some Sensor,
	alarm:    one  Alarm,
	drain:    one  Drain,
}

// Signal signature, used by Sensor
abstract sig Signal {}
one sig Low, Normal, High extends Signal {}

// Alarm state enumeration: On or Off
abstract sig AlarmState {}
one sig AlarmOn, AlarmOff extends AlarmState {}

// Reset state enumeration: On or Off
abstract sig ResetState {}
one sig ResetOn, ResetOff extends ResetState {}

// Valve state enumeration: Open or closed
abstract sig ValveState {}
one sig ValveOpen, ValveClosed extends ValveState {}

// Sensor signature
sig Sensor {
	sensedValue: Signal one -> Time
}

// Console signature
one sig Console {
	resetState: ResetState one -> Time
}

// Drain signature
one sig Drain {
	valveState: ValveState one -> Time
}

// Alarm signature
one sig Alarm {
	alarmState: AlarmState one -> Time
}

// =======================================
// =============== FACTS =================
fact wtpHasThreeSensors{
	all w: WTP | #(w.sensor) = 3
}

//fact oneSignalAtATime{
//	all t:Time | #(AlarmOn + AlarmOff) = 1
//}
//
//fact oneValveStateAtATime{
//	all t:Time | #(ValveOpen + ValveClosed) = 1
//}
//
//fact oneAlarmStateAtATime{
//	all t:Time | #(AlarmOn + AlarmOff) = 1
//}
//
//fact oneResetStateAtATime{
//	all t:Time | #(ResetOn + ResetOff) = 1
//}


// =======================================
// ============ PREDICATES ===============
// Frame conditions
// The reset state should not change between two time steps
pred noResetChange[c: Console, t,t':Time]{
	c.resetState.t = c.resetState.t'
}

// The alarm state should not change between two time steps
pred noAlarmChange[a: Alarm, t,t':Time]{
	a.alarmState.t = a.alarmState.t'
}

// The valve state should not change between two time steps
pred noValveChange[d: Drain, t,t':Time]{
	d.valveState.t = d.valveState.t'
}

// SENSORS/ALARM PREDICATES
// ========================

// We take in consideration a value from the sensors if two or 
// more sensors output the same
//pred twoOrMoreSensorsHigh[w: WTP]{
//	all s: WTP.sensor, t: Time |
//		#(s.sensedValue.t in High) > 2
//}

// Signals can only go to the neighbour LOW <-> NORMAL <-> HIGH
// -> No HIGH then LOW or LOW then HIGH

/* If a HIGH signal is sensed, the next one should not be LOW
** therefore can be HIGH or NORMAL
*/
pred highThenHighOrNormal[w:WTP, s: Sensor, t,t': Time]{
	// PRE CONDITION
	// =============
	s in w.sensor
	s.sensedValue.t in High

	// POST CONDITION
	// ==============
	s.sensedValue.t' in (High + Normal)	
	
	// FRAME CONDITION
	// ===============
	// The reset state is unchanged
	noResetChange[w.console,t,t']
	noValveChange[w.drain,t,t']
}

// If a LOW signal is sensed, the next one should not be HIGH
// therefore can be LOW or NORMAL
pred lowThenLowOrNormal[w:WTP, s: Sensor, t,t': Time]{
	// PRE CONDITION
	// =============
	// State before incoming High signal
	s in w.sensor
	s.sensedValue.t in Low

	// POST CONDITION
	// ==============
	s.sensedValue.t' in (Low + Normal)	
	
	// FRAME CONDITION
	// ===============
	// The reset state is unchanged
	noResetChange[w.console,t,t']
	noValveChange[w.drain,t,t']
}

// An incoming HIGH value from a sensor should trigger the alarm
pred oneHighTriggersAlarm[w: WTP, t,t': Time]{
	// PRE CONDITION
	// =============
	// State before incoming High signal
	w.sensor.sensedValue.t in Normal
	w.alarm.alarmState.t  in AlarmOff
 	// High signal incoming
	w.sensor.sensedValue.t' in High
	
	// POST CONDITION
	// ==============
	// Alarm is triggered
	w.alarm.alarmState.t' in AlarmOn	
	
	// FRAME CONDITION
	// ===============
	// The reset state is unchanged
	noResetChange[w.console,t,t']
	noValveChange[w.drain,t,t']
}

// An incoming LOW value from a sensor should trigger the alarm
pred oneLowTriggersAlarm[w: WTP, t,t': Time]{
	// PRE CONDITION
	// =============
	// State before incoming High signal
	w.sensor.sensedValue.t in Normal
	w.alarm.alarmState.t  in AlarmOff
 	// High signal incoming
	w.sensor.sensedValue.t' in Low
	
	// POST CONDITION
	// ==============
	// Alarm is triggered
	w.alarm.alarmState.t' in AlarmOn	
	
	// FRAME CONDITION
	// ===============
	// The reset state is unchanged
	noResetChange[w.console,t,t']
	noValveChange[w.drain,t,t']
}

// ONE incoming HIGH value from a sensor should trigger the alarm but
// if the next one is back to NORMAL, the alarm should be switched off
pred oneHighThenNormalDisablesAlarm[w: WTP, t,t',t'': Time]{
	// PRE CONDITION
	// =============
	// State before incoming High signal   (t)
	w.sensor.sensedValue.t    in Normal
	w.alarm.alarmState.t      in AlarmOff
	// State before incoming Normal signal (t')
	w.sensor.sensedValue.t'  in High
	w.alarm.alarmState.t'     in AlarmOn
 	// Normal signal incoming 			   (t'')
	w.sensor.sensedValue.t'' in Normal
	
	// POST CONDITION
	// ==============
	w.alarm.alarmState.t''    in AlarmOff	
	
	// FRAME CONDITION
	// ===============
	noResetChange[w.console,t,t']
	noResetChange[w.console,t',t'']
	noValveChange[w.drain,t,t']
	noValveChange[w.drain,t',t'']
}

// Coming from a LOW sensed value, obtaining a NORMAL value
// should switch the alarm off.
pred lowThenNormalDisablesAlarm[w: WTP, t,t': Time]{
	// PRE CONDITION
	// =============
	// Initial LOW signal(s)              (<=t)
	w.sensor.sensedValue.t  in Low
	w.alarm.alarmState.t    in AlarmOn
 	// Normal signal incoming 			   (t')
	w.sensor.sensedValue.t' in Normal
	
	// POST CONDITION
	// ==============
	w.alarm.alarmState.t'   in AlarmOff	
	
	// FRAME CONDITION
	// ===============
	noResetChange[w.console,t,t']
	noValveChange[w.drain,t,t']
}

// CONSOLE PREDICATES
// ==================
pred resetSignalLastsOneTimeStep[w:WTP, t,t',t'':Time]{
	// PRE CONDITION
	// =============
	w.console.resetState.t   in ResetOff
	w.console.resetState.t'  in ResetOn
	// POST CONDITION
	// ==============
	w.console.resetState.t'' in ResetOff
	// FRAME CONDITION
	// ===============
	// Valve can change, Alarm can change
}

// An incoming reset signal should disable the alarm
pred resetDisablesAlarm[w: WTP, t,t': Time]{
	// PRE CONDITION
	// =============
	w.console.resetState.t  in ResetOff
	w.alarm.alarmState.t    in AlarmOn
 	// Reset signal incoming 			   (t')
	w.console.resetState.t' in ResetOn
	
	// POST CONDITION
	// ==============
	w.alarm.alarmState.t'   in AlarmOff	
	
	// FRAME CONDITION
	// ===============
	// Valve will change as well. see resetClosesValve
}

// An incoming reset signal should close the valve
pred resetClosesValve[w: WTP, t,t': Time]{
	// PRE CONDITION
	// =============
	w.console.resetState.t  in ResetOff
	w.drain.valveState.t    in ValveOpen
 	// Reset signal incoming 			   (t')
	w.console.resetState.t' in ResetOn
	
	// POST CONDITION
	// ==============
	w.drain.valveState.t'   in ValveClosed
	
	// FRAME CONDITION
	// ===============
	// Alarm will change as well. see resetDisablesAlarm
}

// An incoming reset signal should not be processed if HIGH values are read
pred noResetIfHighSensed[w:WTP, t,t':Time]{
	// PRE CONDITION
	// =============
	w.console.resetState.t  in ResetOff
	w.sensor.sensedValue.t  in High
 	// Reset signal incoming 			   (t')
	w.console.resetState.t' in ResetOn

	// POST CONDITION
	// ==============
	// Nothing should happen
	
	// FRAME CONDITION
	// ===============
	noAlarmChange[w.alarm,t,t']
	noValveChange[w.drain,t,t']
}

// DRAIN PREDICATES
// ================

// Two incoming HIGH sensed values should open the valve
pred twoHighsOpensValve[w:WTP, t,t':Time]{
	// PRE CONDITION
	// =============
	w.drain.valveState.t  in ValveClosed
	w.sensor.sensedValue.t  in High
 	// Reset signal incoming 			   (t')
	w.drain.valveState.t' in ValveOpen

	// POST CONDITION
	// ==============
	// Nothing should happen
	
	// FRAME CONDITION
	// ===============
	noAlarmChange[w.alarm,t,t']
}

/* Nothing coming from the sensors should be processed while the valve is open
** Split into ignoresHigh, ignoresNormal and ignoresLow
** But ignoresHigh -> No need because it would trigger the alarm (already on if valve open)
**				   -> Two HIGHS should be ignored
**     ignoresLow  -> No need because it would trigger the alarm (already on if valve open)
** So Normal should not disable the alarm
*/
pred valveOpenIgnoresNormalValue[w:WTP, t,t':Time]{
	// PRE CONDITION
	// =============
	// Actual state
	w.drain.valveState.t    in ValveOpen
	w.alarm.alarmState.t    in AlarmOn
	w.sensor.sensedValue.t  in High
 	// Normal signal incoming 			   (t')
	w.sensor.sensedValue.t' in Normal

	// POST CONDITION
	// ==============
	// Nothing should happen
	
	// FRAME CONDITION
	// ===============
	noAlarmChange[w.alarm,t,t']
	noValveChange[w.drain,t,t']
}

pred valveOpenIgnoresTwoHighValues[w:WTP, t,t',t'':Time]{
	// PRE CONDITION
	// =============
	// Actual state
	w.drain.valveState.t    in ValveOpen
	w.alarm.alarmState.t    in AlarmOn
	w.sensor.sensedValue.t  in High
 	// Normal signal incoming 			   (t')
	w.sensor.sensedValue.t'  in High
	w.sensor.sensedValue.t'' in High
	// POST CONDITION
	// ==============
	// Nothing should happen
	
	// FRAME CONDITION
	// ===============
	noAlarmChange[w.alarm,t,t']
	noValveChange[w.drain,t,t']
}


// =======================================
// ================ RUN ==================
run {}

// =======================================
// ============= ASSERTIONS ==============

assert ThreeSensors {
	all w: WTP |
		#(w.sensor) = 3
}


