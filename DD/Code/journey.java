/* A class that represents a journey between two meetings */
class Journey{
    /* The list of all the segments that compose a journey */
    List segments; 
    Date start_hour;
    int duration;
    Location start_pos;
    Location end_pos;
}

class Segment{
    /*The travel mean used in the segment */
    TravelMean mean;
    Location start_pos;
    Location end_pos;
    //The Following two parameters are used by the constraints
    float length; //In kilometers
    int duration; //In minutess
}

class TravelMean{
    List constraints;
}

Journey computeJourney(Meeting meeting, Location start_pos, Location end_pos, Date start_hour){
    /* Uses the Google Maps API to get a list with all the possible journeys with all the possible travel means*/
    ist journeys = MAPS.API.getJourneys(start_pos, end_pos, start_hour);

    /*For each journey retrieves the segments and then checks that the segment 
    complies with the constraints of the travel mean. 
    These constraints include the weather conditions.
    In case the constraints is not respected, the journey is removed from the list.*/
    for journey in journeys{
        for segment in journey.segments
            Boolean error= false;
            for constraint in segment.mean.constraints
                if(!constraint.check(journey){
                    journey.remove(journey);
                    error=true;
                    break;
              }
            if(error)
                break;
    }
    /*Sorts the remaining journeys by duration time*/
    journeys.orderbyDuration();

    /*Checks if a meeting type has a preferred vehicle and in case, selects returns the journey that uses only the preferred travel mean */
    if(meeting.type.hasPreference()){
        int index = journeys.getOfJourneyWithPreferredTravelMean(meeting.type.preference);
        if(index >= 0 )
            return journeys.get(index);
    }
    /* Returns the fastest journey */
    return journeys.first;
}