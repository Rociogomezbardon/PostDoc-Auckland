This project tests the reasoning of a robot that interacts with a complex and changing evironment. 
The world is simulated with a python program called realWorld.py which is updated with a refined ASP called Real_World.sp (located in ASP_files) when there are exogeneous actions, and when the robot interacts in the world by acting or observing. The state of this world is held in a dictionary called dic_RefinedState were the elements of the dictionary are of the form:
'coarse_loc(rob1': 'office2',
'coarse_loc(book2': 'office2',
'in_hand(rob1': 'ref3_book1',
'coarse_in_hand(rob1': 'book1',
'loc(ref3_book2': 'c14'


