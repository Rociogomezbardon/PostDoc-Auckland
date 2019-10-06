import os
import subprocess
import re
from datetime import datetime
class Controller_ToA(object):

	def __init__(self,sparcPath):
		self.toa_pre_asp_file = 'preASP_ToA.txt'
		self.toa_asp_file = 'ASP_ToA.sp'
		self.activities_file = 'activities.txt'

		self.sparcPath = sparcPath
		self.toa_pre_asp_split = []
		self.activities_list = []
		#self.__set_activities_list()
		self.__readAsp()
		self.index_goal = self.toa_pre_asp_split.index("%% Goal")+1
		self.index_conditions = self.toa_pre_asp_split.index("%% Initial Conditions")+2
		self.index_new_activity = self.toa_pre_asp_split.index("%% Needs New Activity?")+3
		self.index_activities = self.toa_pre_asp_split.index("%% Existing Activities")+3


	def __set_activities_list(self):
		reader = open(self.activities_file, 'r')
		activities_text = reader.read()
		reader.close()
		self.activities_list = activities_text.strip().split('\n\n')   # spliting string them in activities
		if(self.activities_list != ['']):
			self.activities_list = [a.split('\n') for a in self.activities_list] # spliting each activity in lines
			if(self.activities_list[-1][-1] == ''): self.activities_list[-1] = self.activities_list[-1][:-1]

	def getActivity(self,initial_conditions,goal):
		start_time = datetime.now()
		self.__writeAsp(initial_conditions,goal)
		activity_name = 0
		new_activity = False
		plan = ""
		start_time_first = datetime.now()
		answer = subprocess.check_output('java -jar ' +self.sparcPath + ' ' + self.toa_asp_file +' -A ',shell=True)
		time_first = (datetime.now() - start_time_first).total_seconds()
		time_second = 0
		if(answer == "{}\n"): 
			print("			&&&&&&&&&&&&& Goal already holds &&&&&&&&&&&&&")
			plan = "Goal holds"
			time = (datetime.now() - start_time).total_seconds()
			return [time, time_first, time_second, new_activity,activity_name,"Goal Holds",len(self.activities_list)]
		elif(answer == "\n"):
			print("			############# NEEDS NEW ACTIVITY #############") 
			self.__writeAspNewActivity(initial_conditions,goal)
			start_time_second = datetime.now()
			answer = subprocess.check_output('java -jar ' +self.sparcPath + ' ' + self.toa_asp_file +' -A ',shell=True) 
			time_second = (datetime.now() - start_time_second).total_seconds()
			chosenAnswer = (answer.split('\n'))[0].strip('}{')
			if chosenAnswer == '': 
				print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! UNABLE TO FIND ACTIVITY !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
				time = (datetime.now() - start_time).total_seconds()
				return [time,new_activity,activity_name,"Inconsistency"]
			self.__updateActivitiesList(chosenAnswer)
			self.__updateActivitiesFile()
			activity_name = int(((chosenAnswer[23:]).split(')'))[0])
			new_activity = True
		elif(answer.startswith("{occurs(select_activity(")): 
			activity_name = int(((answer[24:]).split(')'))[0])
		plan = (self.activities_list[activity_name-1])[1:-1]
		plan = [a[([m.start() for m in re.finditer(',', a)])[1]+1:-2] for a in plan]
		finish_time = datetime.now()
		time = (finish_time - start_time).total_seconds()
		return [time, time_first, time_second, new_activity,activity_name,plan,len(self.activities_list)]

	def __readAsp(self):
		reader = open(self.toa_pre_asp_file, 'r')
		toa_pre_asp = reader.read()
		reader.close()
		self.toa_pre_asp_split = toa_pre_asp.split('\n')


	def __writeAsp(self,initial_conditions,goal):
		new_asp = list(self.toa_pre_asp_split)
		if(self.activities_list==['']): max_name = 1
		else: 	max_name =  len(self.activities_list)+1
		new_asp[0] = "#const max_name = " + str(max_name) + "."

		new_asp.insert(self.index_goal,  "selected_goal("+goal+").")
		new_asp.insert(self.index_conditions,initial_conditions)

		activities_strings = ['\n'.join(activity) for activity in self.activities_list]
		final_string = '\n\n'.join(activities_strings)
		new_asp.insert(self.index_activities,final_string)

		asp = '\n'.join(new_asp)
	        f1 = open(self.toa_asp_file, 'w')
		f1.write(asp) 
		f1.close()


	def __writeAspNewActivity(self,initial_conditions,goal):
		new_asp = list(self.toa_pre_asp_split)
		if(self.activities_list==['']): max_name = 1
		else: 	max_name =  len(self.activities_list)+1
		new_asp[0] = "#const max_name = " + str(max_name) + "."

		new_asp.insert(self.index_goal,  "selected_goal("+goal+").")
		new_asp.insert(self.index_conditions,initial_conditions)
		new_asp.insert(self.index_new_activity,"needs_new_activity.")
		new_asp[-1] = ("activity_goal.\nactivity_component.\nactivity_length.")

		asp = '\n'.join(new_asp)
	       	f1 = open(self.toa_asp_file, 'w')
		f1.write(asp) 
		f1.close()


	def __updateActivitiesList(self,answer):
		answer_split = answer.split(', ')
		new_plan = []
		for s in answer_split:
			if('activity_' in s): new_plan.append(s+'.')
		if(self.activities_list == []): self.activities_list = [new_plan] 
		else: self.activities_list.append(new_plan)


	def __updateActivitiesFile(self):
		activities_strings = ['\n'.join(activity) for activity in self.activities_list]
		final_string = '\n\n'.join(activities_strings)
		writer = open(self.activities_file, 'w')
		writer.write(final_string)
		writer.close()



