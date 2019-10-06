import os
import subprocess
from datetime import datetime
class Controller_Traditional(object):

	def __init__(self,sparcPath):
		self.traditional_pre_asp_file = 'preASP_Traditional.txt'
		self.traditional_asp_file = 'ASP_Traditional.sp'
		self.sparcPath = sparcPath
		self.traditional_pre_asp_split = []
		self.__read_trad_asp()
		self.index_goal = self.traditional_pre_asp_split.index("%% Goal")+1
		self.index_conditions = self.traditional_pre_asp_split.index("%% Initial Conditions")+2

	def getPlan(self,initial_conditions,goal):
		start_time = datetime.now()
		self.__writeAsp(initial_conditions,goal)
		newPlan = []
		answerSet = subprocess.check_output('java -jar ' +self.sparcPath + ' ' + self.traditional_asp_file +' -A ',shell=True)
		if(answerSet == "{}\n"): 
			print("&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&& Goal already holds &&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&")
			newPlan = ['Goal Holds']
		elif(answerSet == "\n"): 
			print("################################ UNABLE TO FIND PLAN ################################")
			newPlan = ['Inconsistency']
		else:
			plans = answerSet.rstrip().split('\n\n') 
    			plans = [plan for plan in plans if plan!='' and plan!='{}']
			chosenPlan = plans[0]
			plan_in_actions = chosenPlan.strip('}').strip('{').split(', ')
			splitActionsList = [action[:-1].split('),') for action in plan_in_actions]
			splitActionsList.sort(key=lambda x:int(x[1])) 
 			plan_in_actions = ['),'.join(action)+ ')' for action in splitActionsList]
			for a in plan_in_actions:
				newPlan.append(a[7:a.rfind(',')])
		finish_time = datetime.now()
		time = (finish_time - start_time).total_seconds()
		return [time,newPlan]


	def __writeAsp(self,initial_conditions,goal):
		new_asp_split = list(self.traditional_pre_asp_split)
		new_asp_split.insert(self.index_goal,"goal(I) :- holds("+goal+",I).")
		new_asp_split.insert(self.index_conditions,initial_conditions)
		asp = '\n'.join(new_asp_split)
	        f1 = open(self.traditional_asp_file, 'w')
		f1.write(asp) 
		f1.close()


	def __read_trad_asp(self):
		reader = open(self.traditional_pre_asp_file, 'r')
		traditional_pre_asp = reader.read()
		reader.close()
		self.traditional_pre_asp_split = traditional_pre_asp.split('\n')

