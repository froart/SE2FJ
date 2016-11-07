// ALLOY SPECIFICATION 
// FOR CARSHARING SYSTEM RASD
// AUTHORS: ARTEMIY FROLOV

// PEOPLE
// ============================================================================

// Person
abstract sig Person{}
// Registered User
sig RegUser extends Person {
car: lone Car // can reserve the car
}
// Unregistered User
sig UnregUser extends Person {}{ 
// unregistered users cannot use a car (can be done in Reqs)
}

// ============================================================================

// CAR
// ============================================================================

// Car occupation states
abstract sig CarOcState {}
sig Available extends CarOcState {}
sig Reserved extends CarOcState {}
sig Occupied extends CarOcState {}
// Car charging states
abstract sig CarChState {}
sig Charging extends CarChState {}
sig Notcharging extends CarChState {}
// Battery fulness
abstract sig BatteryFulness {}
sig More50 extends BatteryFulness {}
sig Less20 extends BatteryFulness {}
sig More20Less50 extends BatteryFulness {}
// Car
sig Car {
occstate: one CarOcState, // wether car is available, reserved or occupied
chastate: one CarChState, // wether car is charging or not 
taken: lone RegUser, // car can either have a RegUser or not
passengers: some Person, // can carry some persons
battery: one BatteryFulness // battery fulness
}

// CONVENTIONS
// ============================================================================



fact { 
no r: RegUser in taken implies state CarState = Available // (Not sure) if no RegUser is in the Car, then Car is available 
#taken <= 1 // redundant?
}
// 1 car can be taken by 1 user
fact UserCarConvention{
all c: Cars, u: User | Car.taken = User.car // ???
}
// Number of people in the car
fact NumberOfPersonsInTheCar {
all c: Car { 
// Number of RegUsers is restricted in Car definition
one RegUser in c.taken implies #Car.passengers <= 5 // If the car is taken by RegUser, itcan take at most 5 persons
no RegUser in c.taken implies #Car.passengers = 0 // if car is not taken by RegUser, no one can be in the car 
// (can be written in more compact way??)
}}
// ============================================================================


// REQUIREMENTS AND DOMAIN ASSUMPTIONS
// ============================================================================
fact {}








// ============================================================================


