boolean makesUnreachable(Meeting prev,Journey journey,Meeting next){
    if(prev.end + journey.duration > next.start){
        return true;
    }
    return false;
}