// ALLOY SPECIFICATION 
// FOR CARSHARING SYSTEM RASD
// AUTHOR: ARTEMIY FROLOV

// PEOPLE
// ==============================

// Any person
abstract sig Person{}
// Registered User
sig RegUser extends Person {
payment: lone Payment
} 
// Unregistered User
sig UnReg extends Person {}

// PAYMENT
// ==============================
// Discounts
abstract sig Discount {}
lone sig Discount10Percent extends Discount {}
lone sig Discount20Percent extends Discount {}
lone sig Discount30Percent extends Discount {}
abstract sig Charge {}
lone sig Euro1 extends Charge{} 

sig Payment {
discounts: set Discount,
charges: set Charge
} {
#discounts >= 0
#charges >= 0
}

// PARKING
// ==============================
abstract sig Parked {}
sig SpecialParkingArea extends Parked{}
sig AnyParkingArea extends Parked {}
lone sig Driven extends Parked{}
// TIME
// ==============================
abstract sig Time {}
lone sig Less1h extends Time{}
lone sig More1h extends Time{}
// CAR
// ==============================
// Car occupation states
abstract sig CarOccupationState {}
lone sig Available extends CarOccupationState {}
lone sig Reserved extends CarOccupationState {}
lone sig Occupied extends CarOccupationState {}
lone sig Released extends CarOccupationState {}
lone sig LostReservation extends CarOccupationState {}
lone sig LostOccupation extends CarOccupationState {}
// Car charging states
abstract sig CarChargingState {}
lone sig Charging extends CarChargingState {}
lone sig NotCharging extends CarChargingState {}
// Battery fulness
abstract sig BatteryFulness {}
lone sig More50 extends BatteryFulness {}
lone sig Less20 extends BatteryFulness {}
lone sig More20Less50 extends BatteryFulness {}
// Engine State
abstract sig CarEngineState {}
lone sig EngineOn extends CarEngineState {}
lone sig EngineOff extends CarEngineState {}
// Car
sig Car {
occupationstate: one CarOccupationState, 
chargingstate: one CarChargingState,
takenby: lone RegUser, 
wastakenby: lone RegUser,
passengers: set Person, 
hadpassengers: set Person,
battery: one BatteryFulness,
parked: one Parked,
enginestate: one CarEngineState,
reservationtime: lone Time
}{
#passengers >= 0
#passengers <= 4
#hadpassengers >= 0
#hadpassengers <= 4
}

// CONVENTIONS
// ==============================

fact TakenWasTakenConventions {
all c: Car | ((c.takenby != none) and (c.occupationstate != Available)) implies (c.wastakenby = none)
all c: Car | ((c.wastakenby != none) and (c.occupationstate != Available)) implies (c.takenby = none)
}

fact OwnerIsAPassenger {
all c: Car | (c.takenby != none) implies (c.takenby in c.passengers)
all c: Car | (c.wastakenby != none) implies (c.wastakenby in c.hadpassengers)
}

fact NoUserCanUseTheSameCar {
all c1, c2: Car | ((c1 != c2) and ((c1.takenby != none) and (c2.takenby != none))) implies (c1.takenby != c2.takenby)
all c1, c2: Car | ((c1 != c2) and ((c1.wastakenby != none) and (c2.wastakenby != none))) implies (c1.wastakenby != c2.wastakenby)
all c1, c2: Car | ((c1 != c2) and ((c1.takenby != none) and (c2.wastakenby != none))) implies (c1.takenby != c2.wastakenby)
}

fact NoTheSamePassengers {
all c1, c2: Car | ((c1 != c2) and (c1.passengers != none) and (c2.passengers != none)) implies (c1.passengers & c2.passengers) = none
all c1, c2: Car | ((c1 != c2) and (c1.hadpassengers != none) and (c2.hadpassengers != none)) implies (c1.hadpassengers & c2.hadpassengers) = none
all c1, c2: Car | ((c1 != c2) and (c1.takenby != none) and (c2.passengers != none)) implies (c1.takenby not in c2.passengers)
all c1, c2: Car | ((c1 != c2) and (c1.wastakenby != none) and (c2.hadpassengers != none)) implies (c1.wastakenby not in c2.hadpassengers)
}

fact TakenByDoesntHavePayment {
all c: Car | (c.takenby != none) implies (no c.takenby.payment)
}

fact NoTheSamePayment {
all c1, c2: Car | ((c1 != c2) and (c1.wastakenby != none) and (c2.wastakenby != none)) implies (c1.wastakenby.payment != c2.wastakenby.payment)
}

fact UsersWithoutTheCarCannotHavePayment {
all c: Car, r: RegUser | ((c.takenby != none) and (r not in c.takenby)) implies (no r.payment)  
all c: Car, r: RegUser | ((c.wastakenby != none) and (r not in c.wastakenby)) implies (no r.payment)  
}

fact NoPaymentWithoutOwner {
all c: Car, p: Payment | ((c.takenby != none) and (p not in c.takenby.payment)) implies (no p)  
all c: Car, p: Payment | ((c.wastakenby != none) and (p not in c.wastakenby.payment)) implies (no p)  
}

fact CarChargingConventions {
all c: Car | (c.chargingstate = Charging) implies (c.parked != Driven)
}

fact CarEngineOffConventions {
all c: Car | c.enginestate = EngineOff implies {
c.parked != Driven
}}

// STATES CONVENTIONS
// ==============================
fact CarIsAvailableConventions {
all c: Car | (c.occupationstate = Available) implies
(

no c.takenby and
no c.wastakenby and
no c.passengers and
no c.hadpassengers and
c.enginestate = EngineOff and
no c.reservationtime
)}

fact CarIsReservedConventions {
all c: Car | (c.occupationstate = Reserved) implies (
c.takenby != none and 
(#c.passengers = 1) and
no c.wastakenby and 
no c.hadpassengers and
c.enginestate = EngineOff and
c.reservationtime = Less1h 
)}

fact CarIsLostReservationConventions {
all c: Car | (c.occupationstate = LostReservation) implies (
(no c.takenby) and 
(no c.passengers) and
(c.wastakenby != none) and
(#c.hadpassengers = 1) and
(c.enginestate = EngineOff) and
(c.reservationtime = More1h) and
(c.wastakenby.payment != none) and
(Euro1 in c.wastakenby.payment.charges)
)}

fact CarIsOccupiedConventions {
all c: Car | (c.occupationstate = Occupied) implies (
(c.takenby != none) and
(no c.wastakenby) and
(no c.hadpassengers) and
(no c.reservationtime)
)}

fact CarIsLostOccupationConventions {
all c: Car | (c.occupationstate = LostOccupation) implies (
(no c.takenby) and
(no c.passengers) and
(c.wastakenby != none) and
(c.hadpassengers != none) and
(c.enginestate = EngineOff) and 
(c.reservationtime = More1h) and
(c.wastakenby.payment != none)
)}

fact CarIsReleasedConventions {
all c: Car |  (c.occupationstate = Released) implies (
(no c.takenby) and 
(no c.passengers) and
(c.wastakenby != none) and
(c.hadpassengers != none) and
(c.enginestate = EngineOff) and
(c.wastakenby.payment != none) and
(no c.reservationtime)
)}

// ENCOURAGEMENT
// ==============================
fact More2PassengersDiscount {
all c: Car, oc: c.occupationstate, p: c.wastakenby.payment | (((oc = Released) or (oc = LostOccupation)) && (#c.hadpassengers > 2)) iff (Discount10Percent in p.discounts)     
}

fact More50PercentEnergyDiscount{
all c: Car, oc: c.occupationstate, p: c.wastakenby.payment | ((( oc = Released) or (oc = LostOccupation)) && (c.battery = More50)) iff (Discount20Percent in p.discounts)  
}

fact ChargingOfTheCarDiscount {
all c: Car, oc: c.occupationstate, p: c.wastakenby.payment | ((( oc = Released) or (oc = LostOccupation)) && (c.chargingstate = Charging) && (c.parked = SpecialParkingArea)) iff (Discount30Percent in p.discounts)   // We suppose that charging of the car can only be done on the special parking area
//
}

// ==============================

// TESTING
// ==============================
// Car is Available
pred available () {
some c: Car | (c.occupationstate = Available) and
(c.parked = AnyParkingArea) and
(c.enginestate = EngineOff)
}
// Car is Reserved
pred reserved () {
some c: Car | (c.occupationstate = Reserved) and
(c.parked = AnyParkingArea) and
(c.enginestate = EngineOff)
}
// User has Lost Reservation
pred lostreservation () {
some c: Car | (c.occupationstate = LostReservation) and
(c.parked = AnyParkingArea) and
(c.enginestate = EngineOff)
}
// Car is Occupied
pred occupied () {
some c: Car | (c.occupationstate = Occupied) and
(c.parked = Driven) and
(c.enginestate = EngineOn)
}
// User has Lost Occupation
pred lostoccupation () {
some c: Car | (c.occupationstate = LostOccupation) and
(c.parked = SpecialParkingArea) and
(c.enginestate = EngineOff)
}
//Car is Released
pred released() {
some c1: Car | (c1.occupationstate = Released) and
(c1.parked = SpecialParkingArea) and
(c1.chargingstate = Charging)
}
// Any
pred any() {
#Car = 1 and
some c: Car | (c.occupationstate = LostReservation)
}
// Empty
pred show {}

//run available for 6
//run reserved for 6
//run lostreservation for 6
//run occupied for 6
//run lostoccupation for 6
run released
//run any for 8
//run show
