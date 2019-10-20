import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;

public class ZTE {
	private static final int INF=0x3f3f3f3f;
	private static int[] minCost=new int[16];//请求的最小代价
	private static boolean sort=false;//逆序搜索（）
	private static double c1=100;//剩余带宽权重系数
	private static double c2=0.01;//初始随机系数（分散选择车厢作用）
	private static double c3=10000;//换道成本
	private static double c4=10000;//分流/汇聚成本参数
	private static int totalCostSum;//总代价
	private static int totalCost;//单个请求的代价
	private static int cnt;//链路的索引
	private static int requestnum=1;//当前配置业务编号
	private static int businessNum;//业务数量(打包后)
	private static int[] head=new int[175];//节点的第一条邻接链路索引
	private static Edge[] edges=new Edge[220*34];//链路
	public static int[][] node = new int[175][];//节点(读文本暂存)
	public static int[][] link = new int[220][];//链路(读文本暂存)
	public static int[][] request = new int[4813][];//请求(读文本暂存)
	private static List<Business> business = new LinkedList<Business>();//原始业务队列
	private static List<Business> business3 = new LinkedList<Business>();//第一次合并后业务队列
	private static List<Business> business4 = new LinkedList<Business>();//第二次合并后业务队列
	private static List<Business> business5 = new LinkedList<Business>();//第二次合并后业务队列的备份（还原业务属性用）
	private static Map<Key,Edge> edgeMap = new HashMap<Key,Edge>();//边（车厢）的哈希图
	private static int[][][] businessRoute=new int[4812][][];//业务的路径+格栅编号
	public static void Search(boolean s){//对所有业务进行寻路
		sort=s;
		int maxdel=1;
		Reset();
		PriorityQueue<Business> queue=new PriorityQueue<Business>();
		businessNum=business4.size();
		for(int i=0;i<businessNum;i++) {
			Business bus=business4.get(i);
			queue.add(bus);
		}
		while(!queue.isEmpty()) {//最大优先队列，每次先取出权重最大的业务
			Business bus=queue.poll();
			int[][]r=null;
            r=dijkstra(bus.startNode,bus.endNode,bus.weight,bus.fakenum);
			if(r!=null) {
				AddRoute(r,bus.fakenum);
/*				int currentcost=CalCost(false);
				int tmp=currentcost-lastcost;
				if(tmp<0) {
					DeleteRoute(bus.fakenum);
					queue.add(bus);
				}
				lastcost=currentcost;*/
			}else {
				bus.route=null;
				if(bus.length!=1) {
					//若没有可行的路径，则拆分成两个业务
					Business bus1=null;
					Business bus2=null;
					if(bus.length%2==0) {//若长度为偶数
					int weight1=0;
					int weight2=0;
				    for(int i=0;i<bus.sons.size()/2;i++) {
				    int ii=bus.sons.get(i);
					weight1+=business.get(ii).weight;}
				    for(int i=bus.sons.size()/2;i<bus.sons.size();i++) {
				    int ii=bus.sons.get(i);
					weight2+=business.get(ii).weight;}
					bus1=new Business(business4.size(),0,bus.startNode,bus.endNode,weight1);
					bus1.length=bus.length/2;
					for(int i=0;i<bus.sons.size()/2;i++) {
					    int ii=bus.sons.get(i);
						bus1.sons.add(ii);}
					bus2=new Business(business4.size()+1,0,bus.startNode,bus.endNode,weight2);
					bus2.length=bus.length/2;
					for(int i=bus.sons.size()/2;i<bus.sons.size();i++) {
					    int ii=bus.sons.get(i);
						bus2.sons.add(ii);}
					}
					else {
					int weight1=0;
					int weight2=0;
				    for(int i=0;i<(bus.sons.size()+1)/2;i++) {
				    int ii=bus.sons.get(i);
					weight1+=business.get(ii).weight;}
				    for(int i=(bus.sons.size()+1)/2;i<bus.sons.size();i++) {
				    int ii=bus.sons.get(i);
					weight2+=business.get(ii).weight;}
					bus1=new Business(business4.size(),0,bus.startNode,bus.endNode,weight1);
			        bus1.length=(bus.length+1)/2;
					for(int i=0;i<(bus.sons.size()+1)/2;i++) {
					    int ii=bus.sons.get(i);
						bus1.sons.add(ii);}
					bus2=new Business(business4.size()+1,0,bus.startNode,bus.endNode,weight2);
					bus2.length=(bus.length-1)/2;
					for(int i=(bus.sons.size()+1)/2;i<bus.sons.size();i++) {
					    int ii=bus.sons.get(i);
						bus2.sons.add(ii);}
					}
					business4.add(bus1);
					business4.add(bus2);
					businessNum+=2;
					queue.add(bus1);
					queue.add(bus2);}
				    else {
					//随机删掉一些业务后，重新搜路，直到可通
					if(Math.random()<0.5) {
					sort=false;
					for(int i=0;i<maxdel;i++) {
						int Num=(int)(Math.random()*businessNum);
						Business b=business4.get(Num);
						if(b.route!=null) {queue.add(b);}
						DeleteRoute(Num);
					}
					maxdel=maxdel+1;
					queue.add(bus);
					}}
			}
		}
		
		//把business4的路径拷贝到business1中；
		for(int i=0;i<business4.size();i++) {
			Business bus4=business4.get(i);
		    if(bus4.route!=null) {
		    for(int j=0;j<bus4.sons.size();j++) {
				Business bus=business.get(bus4.sons.get(j));
				bus.route=bus4.route;
		    }
		    }
		}
	}
	public static void ReSearch(boolean s){//丢掉一些业务后，重新对这些业务进行搜路
				sort=s;
				int maxdel=1;
				PriorityQueue<Business> queue=new PriorityQueue<Business>();
				businessNum=business4.size();
				for(int i=0;i<business4.size();i++) {
					int Num=i;
					Business bus=business4.get(Num);
					if(bus.route!=null) {
					DeleteRoute(Num);
					queue.add(bus);}
				}
				//int lastcost=0;
				while(!queue.isEmpty()) {
					Business bus=queue.poll();
					int[][]r=null;
		            r=dijkstra(bus.startNode,bus.endNode,bus.weight,bus.fakenum);
					if(r!=null) {
						AddRoute(r,bus.fakenum);
/*						int currentcost=CalCost(false);
						System.out.println(totalCost);
						int tmp=currentcost-lastcost;
						lastcost=currentcost;*/
					}else {
						bus.route=null;
						if(bus.length!=1) {
							Business bus1=null;
							Business bus2=null;
							if(bus.length%2==0) {
							int weight1=0;
							int weight2=0;
						    for(int i=0;i<bus.sons.size()/2;i++) {
						    int ii=bus.sons.get(i);
							weight1+=business.get(ii).weight;}
						    for(int i=bus.sons.size()/2;i<bus.sons.size();i++) {
						    int ii=bus.sons.get(i);
							weight2+=business.get(ii).weight;}
							bus1=new Business(business4.size(),0,bus.startNode,bus.endNode,weight1);
							bus1.length=bus.length/2;
							for(int i=0;i<bus.sons.size()/2;i++) {
							    int ii=bus.sons.get(i);
								bus1.sons.add(ii);}
							bus2=new Business(business4.size()+1,0,bus.startNode,bus.endNode,weight2);
							bus2.length=bus.length/2;
							for(int i=bus.sons.size()/2;i<bus.sons.size();i++) {
							    int ii=bus.sons.get(i);
								bus2.sons.add(ii);}
							}
							else {
							int weight1=0;
							int weight2=0;
						    for(int i=0;i<(bus.sons.size()+1)/2;i++) {
						    int ii=bus.sons.get(i);
							weight1+=business.get(ii).weight;}
						    for(int i=(bus.sons.size()+1)/2;i<bus.sons.size();i++) {
						    int ii=bus.sons.get(i);
							weight2+=business.get(ii).weight;}
							bus1=new Business(business4.size(),0,bus.startNode,bus.endNode,weight1);
					        bus1.length=(bus.length+1)/2;
							for(int i=0;i<(bus.sons.size()+1)/2;i++) {
							    int ii=bus.sons.get(i);
								bus1.sons.add(ii);}
							bus2=new Business(business4.size()+1,0,bus.startNode,bus.endNode,weight2);
							bus2.length=(bus.length-1)/2;
							for(int i=(bus.sons.size()+1)/2;i<bus.sons.size();i++) {
							    int ii=bus.sons.get(i);
								bus2.sons.add(ii);}
							}
							business4.add(bus1);
							business4.add(bus2);	
							businessNum+=2;
							queue.add(bus1);
							queue.add(bus2);}
						else {
							if(Math.random()<0.5) {
							sort=false;
							for(int i=0;i<maxdel;i++) {
								int Num=(int)(Math.random()*businessNum);
								Business b=business4.get(Num);
								if(b.route!=null) {queue.add(b);}
								DeleteRoute(Num);
							}
							maxdel=maxdel+1;
							queue.add(bus);
							}}
					}
				}
				
				for(int i=0;i<business4.size();i++) {
					Business bus4=business4.get(i);
				    if(bus4.route!=null) {
				    for(int j=0;j<bus4.sons.size();j++) {
						Business bus=business.get(bus4.sons.get(j));
						bus.route=bus4.route;
				    }
				    }
				}
			}
	public static void Reset() {//单个request文件中的循环重置
      for(Edge e:edgeMap.values()) {
     		 e.reset();
  	  }
      for(int i=0;i<business.size();i++) {
  	    business.get(i).route=null;
      }
      for(int i=0;i<business4.size();i++) {
    	    business4.get(i).route=null;
      }
      business4.clear();
      for(int i=0;i<business5.size();i++) {
    	    business4.add(business5.get(i));
      }
	}
	public static void AllReset() {//不同request文件切换中的全重置
	      for(Edge e:edgeMap.values()) {
	     		 e.reset();
	  	  }
	      business.clear();
	      business3.clear();
	      business4.clear();
	      business5.clear();
	      edgeMap.clear();
	}
	public static void Merge() {//把两个源点和目的点相同的业务合并
		for(int i=0;i<business3.size();i++) {
			boolean merge=false;
			Business bus3=business3.get(i);
			for(int j=0;j<business5.size();j++) {
				Business bus4=business5.get(j);
				if((bus3.startNode==bus4.startNode)&&(bus3.endNode==bus4.endNode)&&(bus3.weight+bus4.weight<=100)) {
					merge=true;
					bus4.weight+=bus3.weight;
					bus4.length+=bus3.length;
					for(int k=bus3.num;k<bus3.num+bus3.length;k++) {bus4.sons.add(k);}
					break;
				}
			}
			if(!merge) {business5.add(bus3);bus3.fakenum=business5.size()-1;
			for(int k=bus3.num;k<bus3.num+bus3.length;k++) {bus3.sons.add(k);}}
		}
	}
    public static void main(String[] args) throws IOException {
		long t1=System.currentTimeMillis(); 
		for(int i=0;i<minCost.length;i++) {
			minCost[i]=INF;
		}
		for(int num=1;num<=15;num++) {
		// TODO Auto-generated method stub
		AllReset();
		requestnum=num;
		readTxt();
		dataInit();
		Merge();
		int itNum=1;//单个请求的循环次数
        for(int i=0;i<itNum;i++) {
        	Search(false);
        	CalCost(true);
        	if(totalCost<minCost[num]) {
        		minCost[num]=totalCost;
        		for(int ii=0;ii<business.size();ii++) 
        		{
        			businessRoute[ii]=business.get(ii).route;
        		}
        	}
        }
		System.out.println("request"+requestnum+":minCost:"+minCost[num]);
		totalCostSum+=minCost[num];
		resultPrint();
		}
		System.out.println("averageCost:"+totalCostSum/15);
		long t2=System.currentTimeMillis();
		System.out.println("Time:"+(t2-t1)+"ms");
	
	}
	public static void readTxt() throws IOException {//读文本
		String s;
		int i;
		BufferedReader in = new BufferedReader(new FileReader("E:/Code/nodeAndLink.txt"));
		s = in.readLine();
		i = 0;
		for (i = 0; i < 175; i++) {
			String[] temp = s.split("\\ ");
			node[i] = new int[temp.length];
			for (int kk = 0; kk < temp.length; kk++) {
				node[i][kk] = Integer.parseInt(temp[kk]);
			}
			s = in.readLine();
		}
		i = 0;
		for(i = 0; i< 220;i++) {
			String[] temp = s.split("\\ ");
			link[i] = new int[temp.length];
			for (int kk = 0; kk < temp.length; kk++) {
				link[i][kk] = Integer.parseInt(temp[kk]);
			}
			s = in.readLine();
		}
		
		in = new BufferedReader(new FileReader("E:/Code/request"+requestnum+".txt"));
		s = in.readLine();
		i = 0;
		for (i = 0; i < 4813; i++) {
			String[] temp = s.split("\\ ");
			request[i] = new int[temp.length];
			for (int kk = 0; kk < temp.length; kk++) {
				request[i][kk] = (int)(Double.parseDouble(temp[kk])*2);
			}
			s = in.readLine();
		}
	}
    public static void dataInit(){//数据初始化
    	//Dijkstra init
        cnt=0;
        for(int i=1;i<=174;i++){
            head[i]=-1;
        }
        //Edge init
		for (int i = 0; i < 220; i++) {
			int start = Math.min(link[i][1], link[i][2]);
			int end = Math.max(link[i][1], link[i][2]);
			int band = 100;
			for(int id=1;id<=34;id++) {//创建MAXID条独立的子链路
			Edge e = new Edge(i+1,start,end,head[start],head[end],band,id);
			edges[cnt]=e;
			head[start]=cnt;
			head[end]=cnt++;
			Key k = new Key(start,end,id);
			edgeMap.put(k, e);}
		}
		//Business init
		int kk=0;
		for (int i = 1; i < 4813; i++ ){
			int start= request[i][1]/2;
            int end=request[i][2]/2;
            double weight=(double)request[i][3]/2;
			business.add(new Business(0,i-1,start,end,weight));
			if(i>1) {
			int pstart= request[i-1][1]/2;
            int pend=request[i-1][2]/2;
            
			if(start!=pstart || end!=pend) {
				kk++;
				business3.add(new Business(kk,i-1,start,end,weight));
			}else {
				if(business3.get(kk).weight+weight>100) {kk++;business3.add(new Business(kk,i-1,start,end,weight));}
				else {business3.get(kk).weight+=weight; business3.get(kk).length++;}
			}}else {
				business3.add(new Business(kk,i-1,start,end,weight));
			}
			
		}
	}
    public static void AddRoute(int[][] route,int Num) {//添加业务的路径，配置调度员
    	Edge pre = null;
    	Business currentbus=business4.get(Num);
    	currentbus.route=route;
		for(int i=0;i<route.length-1;i++) {
			if(i==route.length-2) {//终点车厢设置调度员,且要把终点车厢所在业务的下一个车厢也设置调度员！
	        	int keystart=Math.min(route[i][0],route[i+1][0]);
	        	int keyend=Math.max(route[i][0],route[i+1][0]);
	        	int id=route[i+1][1];
	        	int end=route[i+1][0];
	        	Key k=new Key(keystart,keyend,id);
	        	Edge e=edgeMap.get(k);
        		List<Edge> tmpedgeList = new ArrayList<Edge>();
        		tmpedgeList.add(e);
        		for(int ii=0;ii<e.business.size();ii++) {
        			Business tmpbus=business4.get(e.business.get(ii));
            		int[][] tmproute=tmpbus.route;
            		if(tmproute!=null) {
            		for(int iii=0;iii<tmproute.length;iii++) {
            			if(end==tmproute[iii][0]) {//获得该业务对应操作车厢终点的前车厢和后车厢，并添加到表中
            	        	if(iii<tmproute.length-1) 
            	        		
            	        	{int ks=Math.min(tmproute[iii][0],tmproute[iii+1][0]);
            	        	int ke=Math.max(tmproute[iii][0],tmproute[iii+1][0]);
            				Key kk=new Key(ks,ke,tmproute[iii+1][1]);
            				Edge ee=edgeMap.get(kk);
            				tmpedgeList.add(ee);}//该业务的后车厢（业务很可能没有前车厢）
            	        	
            	        	if(iii>0) {int ks=Math.min(tmproute[iii][0],tmproute[iii-1][0]);
            	        	int ke=Math.max(tmproute[iii][0],tmproute[iii-1][0]);
            				Key kk=new Key(ks,ke,tmproute[iii][1]);
            				Edge ee=edgeMap.get(kk);
            				tmpedgeList.add(ee);}//该业务的前车厢（业务很可能没有后车厢）
            	        	
            			}
            		}}
        		}
        		for(int ii=0;ii<tmpedgeList.size();ii++) {
            		Edge tmpe=tmpedgeList.get(ii);
            		if(end==tmpe.startNode) {tmpe.dds=true;}else {tmpe.dde=true;}
            	}
			}
			int start=route[i][0];
			int id=route[i+1][1];
        	int keystart=Math.min(route[i][0],route[i+1][0]);
        	int keyend=Math.max(route[i][0],route[i+1][0]);
        	Key k=new Key(keystart,keyend,id);
        	Edge e=edgeMap.get(k);
        	e.business.add(Num);
        	e.sum+=Num;
        	e.bandWidthRest=e.bandWidthRest-currentbus.weight;
        	List<Edge> tmpedgeList = new ArrayList<Edge>();
        	tmpedgeList.add(e);
        	PriorityQueue<Integer> tmpbusQueue=new PriorityQueue<Integer>();
        	PriorityQueue<Integer> tmpbusQueuePre=new PriorityQueue<Integer>();
        	for(int ii=0;ii<e.business.size();ii++) {//把该业务后车厢的所有业务添加到表中，把业务对应的前车厢和后车厢添加到表中
        		Business tmpbus=business4.get(e.business.get(ii));
        		tmpbusQueue.add(e.business.get(ii));
        		int[][] tmproute=tmpbus.route;
        		if(tmproute!=null) {
        		for(int iii=0;iii<tmproute.length;iii++) {
        			if(start==tmproute[iii][0]) {//获得该业务对应操作车厢终点的前车厢和后车厢，并添加到表中
        	        	if(iii<tmproute.length-1) 
        	        	{int ks=Math.min(tmproute[iii][0],tmproute[iii+1][0]);
        	        	int ke=Math.max(tmproute[iii][0],tmproute[iii+1][0]);
        				Key kk=new Key(ks,ke,tmproute[iii+1][1]);
        				Edge e1=edgeMap.get(kk);
        				tmpedgeList.add(e1);}//该业务的后车厢
        	        	if(iii>0) {int ks=Math.min(tmproute[iii][0],tmproute[iii-1][0]);
        	        	int ke=Math.max(tmproute[iii][0],tmproute[iii-1][0]);
        				Key kk=new Key(ks,ke,tmproute[iii][1]);
        				Edge e2=edgeMap.get(kk);
        				tmpedgeList.add(e2);}//该业务的前车厢
        			}
        		}}
        		
        		
        	}
        	
        	
        	if(pre!=null) {
        	tmpedgeList.add(pre);
        	for(int ii=0;ii<pre.business.size();ii++) {//把该业务前车厢的所有业务添加到表中，把业务对应的前车厢和后车厢添加到表中
        		Business tmpbus=business4.get(pre.business.get(ii));
        		tmpbusQueuePre.add(pre.business.get(ii));
        		int[][] tmproute=tmpbus.route;
        		if(tmproute!=null) {
        		for(int iii=0;iii<tmproute.length;iii++) {
        			if(start==tmproute[iii][0]) {//获得该业务对应操作车厢终点的前车厢和后车厢，并添加到表中
        	        	if(iii<tmproute.length-1) {int ks=Math.min(tmproute[iii][0],tmproute[iii+1][0]);
        	        	int ke=Math.max(tmproute[iii][0],tmproute[iii+1][0]);
        				Key kk=new Key(ks,ke,tmproute[iii+1][1]);
        				Edge ee=edgeMap.get(kk);
        				tmpedgeList.add(ee);}//该业务的后车厢
        	        	if(iii>0) {int ks=Math.min(tmproute[iii][0],tmproute[iii-1][0]);
        	        	int ke=Math.max(tmproute[iii][0],tmproute[iii-1][0]);
        				Key kk=new Key(ks,ke,tmproute[iii][1]);
        				Edge ee=edgeMap.get(kk);
        				tmpedgeList.add(ee);}//该业务的前车厢
        			}
        		}}	
        	}
        	}
        	
        	boolean diaodu=false;
        	if(pre!=null && e.id!=pre.id) {
        		diaodu=true;
        	}else {
        		if(tmpbusQueue.toString().equals(tmpbusQueuePre.toString())) {
        			diaodu=false;
        		}else {
        			diaodu=true;
        		}
        	}

        	if(diaodu) {
        		//所有表中车厢在该end点的调度员置1。
        		for(int ii=0;ii<tmpedgeList.size();ii++) {
            		Edge tmpe=tmpedgeList.get(ii);
            		if(start==tmpe.startNode) {tmpe.dds=true;}
            		else if(start==tmpe.endNode){tmpe.dde=true;}
            	}
        	};
        	pre=e;
        	}   
    }
    public static void DeleteRoute(int Num) {//删除业务的路径，解除调度员
    	Edge pre = null;
    	Business currentbus=business4.get(Num);
    	int[][] route=currentbus.route;
    	if(route!=null) {
    	currentbus.route=null;
		for(int i=0;i<route.length-1;i++) {
			if(i==route.length-2) {
				boolean diaodu=true;//终点车厢查找该车厢和该车厢任一业务的下一车厢，若完全相同，则取消调度员！（或为空）
	        	int keystart=Math.min(route[i][0],route[i+1][0]);
	        	int keyend=Math.max(route[i][0],route[i+1][0]);
	        	int id=route[i+1][1];
	        	int end=route[i+1][0];
	        	Key k=new Key(keystart,keyend,id);
	        	Edge e=edgeMap.get(k);
	        	for(int ii=0;ii<e.business.size();ii++) {
	        		if(e.business.get(ii)==Num) {
	        			e.business.remove(ii);//将业务从该条链路中删除
	        			e.sum-=Num;
	        		}
	        	}
	        	if(e.business.size()==0) {
	        			e.dds=false;
	        			e.dde=false;
	        	}else {
	        	Business tmpbus=business4.get(e.business.get(0));//获取任意一条业务，查找该业务到start的全部路径
	        	int[][] tmproute=tmpbus.route;
	        	Edge e1=null;
	        	Edge e2=null;
	        	if(tmproute!=null) {
	        	   for(int iii=0;iii<tmproute.length;iii++) {
	        	   if(end==tmproute[iii][0]) {//获得该业务对应操作车厢起点的前车厢和后车厢，并添加到表中
	        	       if(iii<tmproute.length-1) {int ks=Math.min(tmproute[iii][0],tmproute[iii+1][0]);
	        	       int ke=Math.max(tmproute[iii][0],tmproute[iii+1][0]);
	        		   Key kk=new Key(ks,ke,tmproute[iii+1][1]);
	        		   e1=edgeMap.get(kk);
	        		   }//该业务的后车厢
	        	        	if(iii>0) {int ks=Math.min(tmproute[iii][0],tmproute[iii-1][0]);
	        	        	int ke=Math.max(tmproute[iii][0],tmproute[iii-1][0]);
	        				Key kk=new Key(ks,ke,tmproute[iii][1]);
	        				e2=edgeMap.get(kk);
	        				}//该业务的前车厢
	        			}
	        		}}
	        		if(e1==null || e2==null || e1.id!=e2.id) {
	        		   diaodu=true;	
	        		}else {
	    	        	PriorityQueue<Integer> tmpbusQueue1=new PriorityQueue<Integer>();
	    	        	PriorityQueue<Integer> tmpbusQueue2=new PriorityQueue<Integer>();
	        			for(int ii=0;ii<e1.business.size();ii++) {
	                		tmpbusQueue1.add(e1.business.get(ii));}
	        			for(int ii=0;ii<e2.business.size();ii++) {
	                		tmpbusQueue2.add(e2.business.get(ii));}
	        			if(tmpbusQueue1.toString().equals(tmpbusQueue2.toString())) {
	        				diaodu=false;
	        			}else {
	        				diaodu=true;
	        			}
	        		}
	        		if(!diaodu) {
	                	if(end==e1.endNode) {e1.dde=false;}else {e1.dds=false;}
	                	if(end==e2.endNode) {e2.dde=false;}else {e2.dds=false;}
	        		}
	        	}
        		
			}
			boolean diaodu=false;
			int start=route[i][0];
			int id=route[i+1][1];
        	int keystart=Math.min(route[i][0],route[i+1][0]);
        	int keyend=Math.max(route[i][0],route[i+1][0]);
        	Key k=new Key(keystart,keyend,id);
        	Edge e=edgeMap.get(k);
        	for(int ii=0;ii<e.business.size();ii++) {
        		if(e.business.get(ii)==Num) {
        			e.business.remove(ii);//将业务从该条链路中删除
        		}
        	}
        	e.bandWidthRest=e.bandWidthRest+currentbus.weight;//还原链路带宽
        	
        	if(e.business.size()==0) {
        		e.dds=false;
        		e.dde=false;
        	}
        	else{
        	Business tmpbus=business4.get(e.business.get(0));//获取该边包含的任意一条业务，查找该业务到start的全部路径
    		int[][] tmproute=tmpbus.route;
    		Edge e1=null;Edge e2=null;
    		if(tmproute!=null) {
    		for(int iii=0;iii<tmproute.length;iii++) {
    			if(start==tmproute[iii][0]) {//获得该业务对应操作车厢起点的前车厢和后车厢，并添加到表中
    	        	if(iii<tmproute.length-1) {int ks=Math.min(tmproute[iii][0],tmproute[iii+1][0]);
    	        	int ke=Math.max(tmproute[iii][0],tmproute[iii+1][0]);
    				Key kk=new Key(ks,ke,tmproute[iii+1][1]);
    				e1=edgeMap.get(kk);
    				//System.out.println(tmpbus.num+" e1:"+e1.num+",size:"+e1.business.size()+",id:"+e1.id);
    				
    				}//该业务的后车厢
    	        	if(iii>0) {int ks=Math.min(tmproute[iii][0],tmproute[iii-1][0]);
    	        	int ke=Math.max(tmproute[iii][0],tmproute[iii-1][0]);
    				Key kk=new Key(ks,ke,tmproute[iii][1]);
    				e2=edgeMap.get(kk);
    				//System.out.println(tmpbus.num+" e2:"+e2.num+",size:"+e2.business.size()+",id:"+e2.id);
    				
    				}//该业务的前车厢
    			}
    		}}
    		if(e1==null || e2==null || e1.id!=e2.id) {
    		   diaodu=true;
    		}else {
    			PriorityQueue<Integer> tmpbusQueue1=new PriorityQueue<Integer>();
            	PriorityQueue<Integer> tmpbusQueue2=new PriorityQueue<Integer>();
    			for(int ii=0;ii<e1.business.size();ii++) {
            		tmpbusQueue1.add(e1.business.get(ii));}
    			for(int ii=0;ii<e2.business.size();ii++) {
            		tmpbusQueue2.add(e2.business.get(ii));}
    			if(tmpbusQueue1.toString().equals(tmpbusQueue2.toString())) {
    				diaodu=false;
    				
    			}else {
    				diaodu=true;
    			}
    		}
    		if(!diaodu) {
    			//System.out.println(e1.num+" "+e1.startNode+" "+e2.num+" "+e2.startNode+start);
            	if(start==e1.startNode) {e1.dds=false;} else {e1.dde=false;}
            	if(start==e2.startNode) {e2.dds=false;} else {e2.dde=false;}
            	//System.out.println(e1.num+",id:"+e1.id+" dds:"+e1.dds+" dde:"+e1.dde);
            	//System.out.println(e2.num+",id:"+e2.id+" dds:"+e2.dds+" dde:"+e2.dde);
    		}}
        	
        	if(pre!=null && pre.business.size()!=0) {
            diaodu=false;
        	Business tmpbus=business4.get(pre.business.get(0));//获取该边包含的任意一条业务，查找该业务到start的全部路径
    		int[][] tmproute=tmpbus.route;
    		Edge e1=null;Edge e2=null;
    		if(tmproute!=null) {
    		for(int iii=0;iii<tmproute.length;iii++) {
    			if(start==tmproute[iii][0]) {//获得该业务对应操作车厢起点的前车厢和后车厢，并添加到表中
    	        	if(iii<tmproute.length-1) {int ks=Math.min(tmproute[iii][0],tmproute[iii+1][0]);
    	        	int ke=Math.max(tmproute[iii][0],tmproute[iii+1][0]);
    				Key kk=new Key(ks,ke,tmproute[iii+1][1]);
    				e1=edgeMap.get(kk);
    				//System.out.println(tmpbus.num+" e1:"+e1.num+",size:"+e1.business.size()+",id:"+e1.id);
    				
    				}//该业务的后车厢
    	        	if(iii>0) {int ks=Math.min(tmproute[iii][0],tmproute[iii-1][0]);
    	        	int ke=Math.max(tmproute[iii][0],tmproute[iii-1][0]);
    				Key kk=new Key(ks,ke,tmproute[iii][1]);
    				e2=edgeMap.get(kk);
    				//System.out.println(tmpbus.num+" e2:"+e2.num+",size:"+e2.business.size()+",id:"+e2.id);
    				
    				}//该业务的前车厢
    			}
    		}}
    		if(e1==null || e2==null || e1.id!=e2.id) {
    		   diaodu=true;
    		}else {
    			PriorityQueue<Integer> tmpbusQueue1=new PriorityQueue<Integer>();
            	PriorityQueue<Integer> tmpbusQueue2=new PriorityQueue<Integer>();
    			for(int ii=0;ii<e1.business.size();ii++) {
            		tmpbusQueue1.add(e1.business.get(ii));}
    			for(int ii=0;ii<e2.business.size();ii++) {
            		tmpbusQueue2.add(e2.business.get(ii));}
    			if(tmpbusQueue1.toString().equals(tmpbusQueue2.toString())) {
    				diaodu=false;
    				
    			}else {
    				diaodu=true;
    			}
    		}
    		if(!diaodu) {
            	if(start==e1.startNode) {e1.dds=false;} else {e1.dde=false;}
            	if(start==e2.startNode) {e2.dds=false;} else {e2.dde=false;}
    		}}
        	
 		pre=e;}
    }}
    public static int  CalCost(boolean x) {//计算成本（是否输出null路径的业务成本）
    	totalCost=0;
		for(Edge e:edgeMap.values()) {
			 if(e.dds==true) {
				 //System.out.println("dds:"+e.num+",id:"+e.id);
				 totalCost+=1;
			 }
			 if(e.dde==true) {
				 //System.out.println("dde:"+e.num+",id:"+e.id);
				 totalCost+=1;
			 }
		}
		if(x) {
			for(int i=0;i<business.size();i++) {
				if(business.get(i).route==null) {
					totalCost+=100;
				}
			}
		}
	    if(x) {System.out.println("request"+requestnum+":currentCost:"+totalCost);}
	    return totalCost;
    }
    public static int[][] dijkstra(int src,int dst,double weigh,int busNum){//以迪杰斯特拉算法为基础
    	int[] nodeparent = new int[175];
    	int[] currentid = new int[175];
    	int[] currentsize = new int[175];
    	int[] currentsum = new int[175];
    	boolean[] currentpredd = new boolean[175];
    	for(int i=0;i<175;i++) {
    		nodeparent[i] = -1;
    	}
    	boolean[] visited=new boolean[175];
    	double[] distance=new double[175];
        for(int i=0;i<175;i++){
            visited[i]=false;
            distance[i]=INF;
            currentid[i]=0;
            currentsize[i]=0;
            currentsum[i]=0;
            currentpredd[i]=false;
            
        }
        PriorityQueue<Node> queue=new PriorityQueue<Node>();
        distance[src]=0;
        queue.add(new Node(src,-1));
        Node tempnode;
        while(!queue.isEmpty()){
        	tempnode=queue.poll();
            int u=tempnode.node;
            if(visited[u]){
                continue;
            }
            visited[u]=true;
            boolean add=false;
            for(int i=head[u];i!=-1;i=(u==edges[i].startNode)?edges[i].startNext:edges[i].endNext){
            
/*            	c1=100;//剩余带宽的参数
            	c2=1;//初始Math.random的参数
            	c3=10000;//换车厢成本
            	c4=10000;//分流成本
*/            	
            	Edge e=edges[i];
            	int id=e.id;
            	int size=e.business.size();
                int v=(u==e.startNode)?e.endNode:e.startNode;
                int sum=e.sum;
                double w=c2*Math.random()+c1*(1/e.bandWidthRest);//1.权值和剩余带宽有关
                boolean afterdd=false;
                boolean equal=false;
                boolean empty=false;
                if((e.startNode==u&&e.dds) || (e.endNode==u&&e.dde)) {
                	afterdd=true;
                }
                if(size==currentsize[u] && sum==currentsum[u] && id==currentid[u]) {
                	//System.out.println("equal");
                	equal=true;
                }
                if(size==0 && currentsize[u]==0 && id==currentid[u]) {
                	empty=true;
                }
                if(!afterdd && u!=src) {w+=(id==currentid[u])?0:c3;}//1.后车厢（边e：u->v）无调度员，加一次换车厢成本
                if(!currentpredd[u] && u!=src) {w+=(id==currentid[u])?0:c3;}//2.前车厢(到u的路)无调度员，加一次换车厢成本           
                w+=c4*0.01;//前车厢和后车厢都有调度员，也要加一次分流和汇聚成本（因为可能影响朋友业务的车厢）
                if(!afterdd) {w+=c4;}//后车厢无调度员，加一次分流和汇聚成本
                if(!currentpredd[u]) {w+=c4;}//后车厢无调度员，加一次分流和汇聚成本
                if(equal) {w=0.1;}
                if(empty) {w=0.01;}
                if(e.bandWidthRest-weigh<0){w=INF;}//5.带宽超限，路不通
                
                if(!visited[v] && distance[v]>distance[u]+w){
                	distance[v]=distance[u]+w;
                	currentid[v]=id;
                	currentsize[v]=size;
                	currentpredd[v]=(v==e.startNode)?e.dds:e.dde;
                	currentsum[v]=e.sum;
                	add=true;
                }
                if(!visited[v] && id==1 && add) {
                    queue.add(new Node(v,distance[v]));
                    nodeparent[v]=u;
                    add=false;
                }
            }
        }
        int parent=dst;
        int routelength=0;
        int[] routetemp=new int[100];
        while(parent!=-1) {
        	routetemp[routelength]=parent;
        	parent=nodeparent[parent];
        	routelength++;
        }
        int[][] route=new int[routelength][2];
        for(int i=0;i<routelength;i++) {
        	route[i][0]=routetemp[routelength-1-i];
        	route[i][1]=currentid[route[i][0]];
        }
        if(distance[dst]>=INF) {
        	//System.out.println("Dijkstra---src:"+src+",dst:"+dst+":No route");
        	route=null;
        	}else {
        //for(int i=0;i<route.length;i++) {System.out.print("e:"+route[i][0]+",id:"+route[i][1]+" -> ");}
        		}
        //System.out.println("dis:"+distance[dst]);
        return route;
    }
    public static void resultPrint() throws IOException{//写文本
   	   String []result = null ;
   	   int businessNum=4812;
   	   result = new String[3*businessNum+1];
   	   result[0] = String.valueOf(businessNum)+" "+String.valueOf(minCost[requestnum]);
   	   for (int i = 1; i < 3*businessNum+1; i=i+3) {
   		Business bus=business.get(i/3);
   		if(bus.weight % 1 != 0) {result[i] = i/3+1 + " "+bus.startNode+" "+bus.endNode+" "+String.format("%.1f", bus.weight);;}
   		else {result[i] = i/3+1 + " "+bus.startNode+" "+bus.endNode+" "+(int)bus.weight;	}
  		int[][] r=businessRoute[i/3];
   		StringBuilder s=new StringBuilder();
   		StringBuilder ss=new StringBuilder();
   		if(r!=null){for (int k = 0; k < r.length-1; k++) {			
  			if(k < r.length - 2){
  				Key key=new Key(Math.min(r[k][0],r[k+1][0]),Math.max(r[k][0],r[k+1][0]),1);
  				Edge edge=edgeMap.get(key);
  				s.append(edge.num).append(" ");
  			}else{
  				Key key=new Key(Math.min(r[k][0],r[k+1][0]),Math.max(r[k][0],r[k+1][0]),1);
  				Edge edge=edgeMap.get(key);
  				s.append(edge.num);
  			}
  		}
   	    result[i+1] = s.toString();
   		for (int k = 1; k < r.length; k++) {			
  			if(k < r.length - 1){
  				ss.append(r[k][1]).append(" ");
  			}else{
  				ss.append(r[k][1]);
  			}
  		}
   	    result[i+2] = ss.toString();}else {
   	    	result[i+1]=null;
   	    	result[i+2]=null;
   	    }
   	   }
       
   	   BufferedWriter out = new BufferedWriter(new FileWriter("E:/Code/1/result"+requestnum+".txt"));
   	   for(int i=0;i<result.length;i++) {
   		  out.write(result[i]+"\r\n");
   		  out.flush();
   	   }
      }
    public static class Business implements Comparable<Business>{//业务类
    	private int fakenum;//合并后的假编号
    	private int num;//真编号
    	private int length;//长度（未合并为1）
		private double weight;//权重
		private int startNode;//起点
		private int endNode;//终点
		private int[][] route;//已寻路径
		private List<Integer> sons;//合并业务包含的子业务
		public Business(int fakenum,int num,int startNode,int endNode,double weight) {
			this.fakenum=fakenum;
			this.num = num;
			this.weight = weight;
			this.startNode = startNode;
			this.endNode = endNode;
			this.length = 1;
			this.route = null;
			this.sons = new ArrayList<Integer>();
		}
        public int compareTo(Business o) {//优先队列的比较,sort为真时为最小优先队列
            if(weight>o.weight){
            	if(sort) {
                return 1;}else {
                return -1;
                }
            }else if(weight==o.weight){
                return 0;
            }else{
            	if(sort) {
                return -1;}else {
                return 1;}
            }
        }
	    }
	public static class Key {//钥匙
		   Integer start;
		   Integer end;
		   Integer id;

		       public Key(int start ,int end,int id) {
			        this.start = start;
		            this.end = end;
		            this.id =id;
		       }

			@Override
			public String toString() {
				return this.start+"->"+this.end+"->"+this.id;
			}

			@Override
			public boolean equals(Object obj) {
			    boolean result = false;
			    if (this == obj)
				result = true;
			    if (obj == null || getClass() != obj.getClass())
				result = false;
			    Key k = (Key) obj;
			    if (k.start == null || k.end == null || k.id == null)
				result = false;
			    if ((k.start.equals(start)) && (k.end.equals(end)) && (k.id.equals(id)))
				result = true;
			    return result;

			}

			@Override
			public int hashCode() {
			    int a = 0;
			    if (start != null && end != null && id !=null) {
				a = start.hashCode() + end.hashCode() + id.hashCode();
			    }
			    return a;

			}
		   
		  
		}
	public static class Edge{//边（车厢）
		    private boolean dds;//起点是否安排了调度员
		    private boolean dde;//终点是否安排了调度员
		    private int num;//路径的编号
		    private int id;//车厢的编号
		    private int startNode;//起点
			private int endNode;//终点
			private int startNext;//起点的第一条邻接边
			private int endNext;//终点的第一条邻接边
			private int bandWidth;//车厢容量
			private double bandWidthRest;//车厢剩余容量
			private List<Integer> business=new ArrayList<Integer>();//车厢承载的业务
			private int sum;//承载业务编号之和
			
			public Edge(int num,int startNode,int endNode,int startNext,int endnext,int bandWidth,int id) {
				this.num=num;
				this.startNode=startNode;
				this.endNode = endNode;
				this.startNext =startNext;
				this.endNext = endnext;
				this.bandWidth = bandWidth;
				this.bandWidthRest = bandWidth;
				this.id=id;
				this.sum=0;
			}
			public void reset() {
				this.dds=false;
				this.dde=false;
				this.bandWidthRest=this.bandWidth;
				this.business.clear();
				this.sum=0;
			}	
			public double avr() {
				if(business.size()!=0) {
				return sum/business.size();}
				else {
				return 0;
				}
			}
			
		}
	public static class Node implements Comparable<Node>{//节点（仅Dijkstra用）
	        public int node;//节点编号
	        public double cost;//权重
	        public Node(int node, double cost) {
	            this.node = node;
	            this.cost=  cost;
	        }
	        public int compareTo(Node o) {//最小优先队列
	            if(cost>o.cost){
	                return 1;
	            }else if(cost==o.cost){
	                return 0;
	            }else{
	                return -1;
	            }
	        }
	    }}
