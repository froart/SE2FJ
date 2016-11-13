// ALLOY SPECIFICATION 
// FOR CARSHARING SYSTEM RASD
// AUTHOR: ARTEMIY FROLOV

// PEOPLE
// ============================================================================

// Any person
abstract sig Person{}
// Registered User
sig RegUser extends Person {
payment: lone Payment
} 
// Unregistered User
sig UnReg extends Person {}






// PAYMENT
// ============================================================================
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
// ============================================================================
abstract sig Parked {}
sig SpecialParkingArea extends Parked{}
sig AnyParkingArea extends Parked {}
lone sig Driven extends Parked{}


// TIME
// ============================================================================
abstract sig Time {}
lone sig Less1h extends Time{}
lone sig More1h extends Time{}

// CAR
// ============================================================================

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
occupationstate: one CarOccupationState, // wether car is available, reserved, occupied or released
chargingstate: one CarChargingState, // wether car is charging or not 
takenby: lone RegUser, // car can either have a RegUser or not
wastakenby: lone RegUser, // 
passengers: set Person, // can carry some persons
hadpassengers: set Person,
battery: one BatteryFulness, // battery fulness
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
// ============================================================================


// OK
fact TakenWasTakenConventions {
all c: Car | ((c.takenby != none) and (c.occupationstate != Available)) implies (c.wastakenby = none)
all c: Car | ((c.wastakenby != none) and (c.occupationstate != Available)) implies (c.takenby = none)
}

// Owners of the car are in passengers OK
fact OwnerIsAPassenger {
all c: Car | (c.takenby != none) implies (c.takenby in c.passengers)
all c: Car | (c.wastakenby != none) implies (c.wastakenby in c.hadpassengers)
}

// OK
fact NoUserCanUseTheSameCar {
all c1, c2: Car | ((c1 != c2) and ((c1.takenby != none) and (c2.takenby != none))) implies (c1.takenby != c2.takenby)
all c1, c2: Car | ((c1 != c2) and ((c1.wastakenby != none) and (c2.wastakenby != none))) implies (c1.wastakenby != c2.wastakenby)
all c1, c2: Car | ((c1 != c2) and ((c1.takenby != none) and (c2.wastakenby != none))) implies (c1.takenby != c2.wastakenby)
}
// OK
fact NoTheSamePassengers {
all c1, c2: Car | ((c1 != c2) and (c1.passengers != none) and (c2.passengers != none)) implies (c1.passengers & c2.passengers) = none
all c1, c2: Car | ((c1 != c2) and (c1.hadpassengers != none) and (c2.hadpassengers != none)) implies (c1.hadpassengers & c2.hadpassengers) = none
all c1, c2: Car | ((c1 != c2) and (c1.takenby != none) and (c2.passengers != none)) implies (c1.takenby not in c2.passengers)
all c1, c2: Car | ((c1 != c2) and (c1.wastakenby != none) and (c2.hadpassengers != none)) implies (c1.wastakenby not in c2.hadpassengers)
}

// OK
fact TakenByDoesntHavePayment {
all c: Car | (c.takenby != none) implies (no c.takenby.payment)
}

// No the same payment by users OK
fact NoTheSamePayment {
all c1, c2: Car | ((c1 != c2) and (c1.wastakenby != none) and (c2.wastakenby != none)) implies (c1.wastakenby.payment != c2.wastakenby.payment)
}


// Users that didn't used the car cannot have payment
fact UsersWithoutTheCarCannotHavePayment {
all c: Car, r: RegUser | ((c.takenby != none) and (r not in c.takenby)) implies (no r.payment)  
all c: Car, r: RegUser | ((c.wastakenby != none) and (r not in c.wastakenby)) implies (no r.payment)  
}


// Users that didn't used the car cannot have payment

fact NoPaymentWithoutOwner {
all c: Car, p: Payment | ((c.takenby != none) and (p not in c.takenby.payment)) implies (no p)  
all c: Car, p: Payment | ((c.wastakenby != none) and (p not in c.wastakenby.payment)) implies (no p)  
}



// ???? 
/*
fact NoPaymentWithoutOwner {
all c: Car, p: Payment | p not in c.wastakenby.payment implies (no p)
}
*/


fact CarChargingConventions {
all c: Car | (c.chargingstate = Charging) implies (c.parked != Driven)
}


fact CarEngineOffConventions {
all c: Car | c.enginestate = EngineOff implies {
c.parked != Driven
}}

// occupationstate: one CarOccupationState, // wether car is available, reserved, occupied or released
/* Available state implies:
1. no RegUser in Car.takenby, no passengers
2. must be parked
3. can be charged
4. no reservationtime
5. no payment
6. Engine is off ahahah
*/
fact CarIsAvailableConventions {
all c: Car | (c.occupationstate = Available) implies
(
//no c.takenby
no c.takenby and
no c.wastakenby and
no c.passengers and
no c.hadpassengers and
c.enginestate = EngineOff and
no c.reservationtime
)}


/* Reserved state implies:
1.1. RegUser in Car.takenby, 
1.2. no passengers. It means that Car.takenby has RegUser, but neither RegUser is in Car.passengers nor any other Person
2. must be parked
3. can be charged
4.1. reservation time must be set. 
5. User don't have payment
6. engine off
*/

fact CarIsReservedConventions {
all c: Car | (c.occupationstate = Reserved) implies (
c.takenby != none and 
(#c.passengers = 1) and
no c.wastakenby and 
no c.hadpassengers and
c.enginestate = EngineOff and
c.reservationtime = Less1h 
)}


/*LostReservation state implies
1.1. No RegUser in Car.takenby
1.2. No passengers
2. Engine must be off
3. reservationtime must be More1h
4. User must have payment 1 euro
*/

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

/*
fact Euro1AlwaysAndOnlyAfterLostReservation {
all c: Car | ((Euro1 != none) and (Euro1 in c.wastakenby.payment.charges)) implies (c.occupationstate = LostReservation)
}
*/


/* Occupied state implies:
1.1. RegUser in Car.takenby, 
1.2. can be passengers.
2. can be driven or parked
3. can be charged
4. no reservationtime
5. User don't have payment
*/

fact CarIsOccupiedConventions {
all c: Car | (c.occupationstate = Occupied) implies (
(c.takenby != none) and
(no c.wastakenby) and
(no c.hadpassengers) and
(no c.reservationtime)
)}


/*LostOccupation state implies
1.1 no RegUser in Car.takenby. 
1.2. Can be any passengers
2. Can be charged
3. 
USer must have payment
*/

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




/* Released state implies:
1. no RegUser in Car.takenby, no passengers
2. engine is off
3. can be charged
4. User must have payment
5. no time
*/

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


// ============================================================================

// ENCOURAGEMENT
// ============================================================================

// 2 passengers discount????
fact More2PassengersDiscount {
all c: Car, oc: c.occupationstate, p: c.wastakenby.payment | (((oc = Released) or (oc = LostOccupation)) && (#c.hadpassengers > 2)) iff (Discount10Percent in p.discounts)     
}

/*
fact Disc10Convention {
all c: Car | (Discount10Percent in c.wastakenby.payment.discounts) iff (#c.hadpassengers > 2)
}
*/

// 50% full battery discount
fact More50PercentEnergyDiscount{
all c: Car, oc: c.occupationstate, p: c.wastakenby.payment | ((( oc = Released) or (oc = LostOccupation)) && (c.battery = More50)) iff (Discount20Percent in p.discounts)  
}
// Charging on the special parking zone discount
fact ChargingOfTheCarDiscount {
all c: Car, oc: c.occupationstate, p: c.wastakenby.payment | ((( oc = Released) or (oc = LostOccupation)) && (c.chargingstate = Charging) && (c.parked = SpecialParkingArea)) iff (Discount30Percent in p.discounts)   // We suppose that charging of the car can only be done on the special parking area
//
}

// ============================================================================

// TESTING
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
