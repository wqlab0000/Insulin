//Given("^insulin pump is turned on$")

public class Clock {
    //@ public model long _time;
    //@ private represents _time = second + minute*60 + hour*60*60;
    
    //@ public invariant _time == getSecond() + getMinute()*60 + getHour()*60*60;
    //@ public invariant 0 <= _time && _time < 24*60*60;
    
    //@ private invariant 0 <= hour && hour <= 23;
    private int hour; //@ in _time;
    //@ private invariant 0 <= minute && minute <= 59;
    private int minute; //@ in _time;
    //@ private invariant 0 <= second && second <= 59;
    private int second; //@ in _time;
    //@ private invariant 0 <= read;
    private int read; //@ in _time;

    
//When("^insulin pump glucose reading level time is setted$")

    
    //@ ensures _time == 12*60*60;
    public /*@ pure @*/ Clock() { hour = 12; minute = 0; second = 0; }
    
    //@ ensures 0 <= \result && \result <= 23;
    public /*@ pure @*/ int getHour() { return hour; }
    
    //@ ensures 0 <= \result && \result <= 59;
    public /*@ pure @*/ int getMinute() { return minute; }
    
    //@ ensures 0 <= \result && \result <= 59;
    public /*@ pure @*/ int getSecond() { return second; }
    
    /*@ requires 0 <= hour && hour <= 23;
     @ requires 0 <= minute && minute <= 59;
     @ ensures _time == hour*60*60 + minute*60;
     @*/
    public void setReadGlucoseTime(int hour, int minute){
    this.hour = hour; this.minute = minute; this.second = 0;
     }

//Then("^insulin pump reads glucse every n (\\d+) seconds$")
    
    //@ ensures _time == \old(_time + 1) % 24*60*60;
    public void read_glucose() {
      read = read % (5*60*second);// read glucose every 5 mins
        read++;
      second++;
      if (second == 60) {second = 0; minute++; }
      if (minute == 60) {minute= 0; minute++; }
      if (hour == 24)   {hour = 0;}
 }
    
    
 }

   
