boolean isOverlapped(Meeting meeting, List meetings){
    for(i=0; i< meetings.length; i++){
        if(meetings[i].start >= meeting.start && meetings[i].start <=meeting.end){
            return true;
        }else if(meetings[i].end >= meeting.start && meetings[i].end<=meeting.end){
            return true;
        }
    }
    return false;
}