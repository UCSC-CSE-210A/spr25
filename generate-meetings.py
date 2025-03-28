# pip3 install python-networkdays
from networkdays import networkdays
import holidays
import datetime
import pytz

INSTR_BEGINS = datetime.date(2025, 3, 31)
INSTR_ENDS = datetime.date(2025, 6, 6)

ucsc_holidays = [ "Labor Day"
, "Veterans Day"
, "Thanksgiving"
, "Martin Luther King Jr. Day"
, "Presidents’ Day"
# , "Cesar Chavez Day"
, "Memorial Day"
, "Juneteenth"
, "Independence Day"
, "Labor Day"
]
us_holidays = holidays.US(subdiv='CA', years=INSTR_BEGINS.year)
# Create the list of relevant holidays
HOLIDAYS = [date for date, name in 
              sorted(us_holidays.items())
              if len(list(filter(lambda h: h in name,ucsc_holidays))) > 0 and date >= INSTR_BEGINS and date <= INSTR_ENDS and date.weekday() < 5]

# Update this with the days class DOES NOT meet
# DAYS_OFF = {1,3,5,6,7} # TuTh meetings
DAYS_OFF = {2,4,6,7} # MWF meetings

tz = pytz.timezone('US/Pacific')
days = networkdays.Networkdays(INSTR_BEGINS, INSTR_ENDS, HOLIDAYS, DAYS_OFF).networkdays()
datetimes = [ tz.localize(datetime.datetime(d.year, d.month, d.day), is_dst=None) for d in days ]
print("days:")
for date in datetimes:
   print('  - {date}'.format(date=date))
print('')
holiday_datetimes = [ tz.localize(datetime.datetime(d.year, d.month, d.day), is_dst=None) for d in HOLIDAYS ]
print("holidays:")
for date in holiday_datetimes:
   print('''  - description: {name}
    hide_time: true
    date: {date}
    type: raw_event
    name: Holiday
    color: "#e9ffdb"\n'''.format(name=us_holidays[date], date=date))
