sig Position{}
sig Text{}

/*
Time represents a date.
day: number of days passed since the default day
minute: number of minutes passed since the default day
The control to check if  the number of minutes is coherent with the day 
isn't actually performed, but it is supposed to be always true
*/
sig Time{
    timestamp: one Int,
    day: one Int
}
{
    day > 0
    timestamp > 0
}

// An event is composed by two times: start and end.
abstract sig Event{
    start: one Time,
    end: one Time
}
{
    start.timestamp < end.timestamp 
    start.day = end.day //An event starts and ends in the same day
}

/*
The slot is the range of time in which the Break can be scheduled.
The slot must be in the same day of the start and end dates
*/
sig Break extends Event{
    slotstart: one Time,
    slotend: one Time
}
{
    slotstart.timestamp <= start.timestamp
    slotend.timestamp >= end.timestamp
    slotstart.timestamp < slotend.timestamp
    slotend.day= slotstart.day
    slotstart.day = start.day
}

sig Lunch extends Break{}

sig Meeting extends Event{
    name: one Text,
    desc: one Text,
    position: one Position,
    type: one EventType
}

/*
For each Event Type there is a preferred travel mean 
*/
abstract sig EventType{
    prefers: one TravelMean
}
one sig Family extends EventType{}
one sig Work extends EventType{}
one sig Personal extends EventType{}

one sig User{
	home: one Home,
	currpos: one Position, //The current position of the user
	passes: set TravelPass
}

one sig Home{
	pos: one Position
}

sig Journey{
	user: one User,
/*
	The starting meeting of the journey, null if the user starts from home
*/
	startmeet: lone Meeting, 
	endmeet: one Meeting, // The ending meeting of the journey
	start: one Position, //The starting position
	end: one Position, // The end position
	startseg: one Segment,
	endseg: one Segment,
	intseg: set Segment, 
	day: one Int //The day in which the journey happens
}{
   start != end //The journey must connect two different positions 
   end = endmeet.position
	startmeet != endmeet //The two meetings must be different
	/* If the user starts from home, the start position is the home position, otherwise
	it is the position of the starting (previous) meeting */
	#startmeet = 1 implies start = startmeet.position && (startmeet.start).day = (endmeet.start).day 
																&& (startmeet.start).timestamp < (endmeet.start).timestamp
								else start = (user.home).pos
  
		day = (endmeet.start).day
	/*
    Concatenation of segments, checks that the path is linear and that there are no repeated segments
	It also checks that the starting position of the first segment is equal to the starting position of the journey
	and that the ending position of the ending segment is equal to the ending position of the journey
    */
	startseg.start=start
    endseg.end = end
    no x: intseg | x=startseg || x=endseg
    lone x: intseg | x.start = startseg.end
    lone x: intseg | endseg.start = x.end
    no x: intseg | startseg.start = x.end
    no x:intseg | x.start= endseg.end
    all x: intseg | x.end = endseg.start 
        or one x1: intseg | x.end = x1.start 
    all x: intseg | x.start = startseg.end 
        or one x1: intseg | x.start = x1.end 
    #intseg = 0 implies (startseg = endseg or startseg.end=endseg.start)
}

sig Segment{
	id: one Int, //Unique
	start: one Position,
	end: one Position,
	mean: one TravelMean,
	pass: lone TravelPass, // null if no travel pass is used
	journey: one Journey
}
{
   id >0
   start != end
	/* The travel pass must be valid */
	#pass=1 implies mean = pass.mean && 	journey.day>= (pass.start).day
						 && journey.day <= (pass.end).day
}

abstract sig TravelMean{
	constr: set Constraint,
	pollution: one Level
}
abstract sig PublicTransport extends TravelMean{}
one sig Bus extends PublicTransport{}
one sig Train extends PublicTransport{}
abstract sig SharedVehicle extends TravelMean{}
one sig Bike extends SharedVehicle{}
abstract sig OwnedVehicle extends TravelMean{}
one sig Car extends OwnedVehicle{}
one sig Walk extends OwnedVehicle{}

abstract sig Constraint{}

abstract sig Level{}
one sig Level1 extends Level{}
one sig Level2 extends Level{}
one sig Level3 extends Level{}

sig TravelPass{
	start: one Time,
	end: one Time,
	mean: one PublicTransport
}
{
    start.day <= end.day 
}

/* --------------------------------------------------
FACTS
*/ --------------------------------------------------

//All events must be disjoint and not overlapping
fact allEventDisjoint{
	all disj e1,e2: Event | ((e1.start).timestamp) > ((e2.end).timestamp) 
								|| ((e2.start).timestamp) > ((e1.end).timestamp)
}

//The ID of segments must be unique
fact noSegWithSameId{
	no disj s1,s2: Segment | s1.id = s2.id
}

//A segment  to exist must belong to a journey
fact eachSegBelongsToOneJourney{
	all s: Segment | one j:Journey | (s in j.intseg || s=j.startseg || s=j.endseg)
	all s: Segment |one j:Journey | s.journey = j
}

//We make sure that if on a day there is a meeting, there is also one and only one lunch
fact oneLunchADay{
	all disj l1,l2: Lunch | (l1.start).day != (l2.start).day
	all m:Meeting | one l:Lunch | (l.start).day = (m.start).day
}

//We make sure that a journey is created together with a meeting
fact aMeetingNeedsAJourney{
	all m: Meeting | one j: Journey | j.endmeet = m
	all m: Meeting | lone j: Journey | j.startmeet = m
}

//The user must own a travel pass to use it
fact travelPassMustBeOwned{
	all p: TravelPass | one u:User | p in u.passes
}

//We make sure that only one journey a day starts from home
fact atMostOneJourneyAtADayStartsFromHome{
	all disj j1,j2: Journey | (j1.day=j2.day && #j1.startmeet = 0) implies #j2.startmeet = 1
}

/*The number of journeys is always equal to the number of meeting
	In this ways we make sure that the user every day makes a journey from home*/
fact journeyNumber{
	#Journey = #Meeting
}

/*---------------------------------------------------
	ASSERTIONS
*/ --------------------------------------------------

//Checks that all events are disjoint
assert allEventsDisjoint{
	no disj e1,e2: Event | (e2.start.timestamp > e1.start.timestamp &&  e2.start.timestamp < e1.end.timestamp)
											|| (e2.end.timestamp > e1.start.timestamp &&  e2.end.timestamp < e1.end.timestamp)
}

//Checks that if on a day there is a meeting, there is a lunch
assert ifThereIsAMeetingThereIsLunch{
	no m:Meeting | all l:Lunch | (l.start).day != (m.start).day
}

//Checks that the lunch is always scheduled in the range
assert lunchIsAlwaysInTheLunchSlot{
	no l:Lunch | l.start.timestamp < l.slotstart.timestamp ||  l.end.timestamp > l.slotend.timestamp
}

//Checks that the journey that leaves from home is the first of the day
assert journeyFromHomeFirstOfTheDay{
	no disj j1,j2: Journey | j1.day=j2.day && #j1.startmeet = 0 && #j2.startmeet = 0
}

//Checks that tickets used in a segment are valid
assert usedTicketsAreValidDuringTheSegment{
	all s:Segment | #s.pass = 1 implies s.pass.start.day <= s.journey.day && s.pass.end.day >= s.journey.day
}

/*
	PREDICATES
*/
/*This generated a simplified world,
 with the schedule of one day in which there are 2 meetings and three segments along two journeys
*/
pred show(){
	(Meeting.start).day=3
	#Meeting = 2 
	#Segment = 3
	#Position = 4
	#TravelPass = 1
}

check lunchIsAlwaysInTheLunchSlot for 6 but 5 int
check ifThereIsAMeetingThereIsLunch for 6 but 5 int
check allEventsDisjoint for 6 but 5 int
check journeyFromHomeFirstOfTheDay for 6 but 5 int
check  usedTicketsAreValidDuringTheSegment for 6 but 5 int
run show for 6 but 5 int
