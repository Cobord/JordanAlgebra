import pickle, time
from chain2 import aut_O
t=time.time(); A=aut_O(); print(len(A), round(time.time()-t,1))
pickle.dump(A, open('autO.pkl','wb'))
