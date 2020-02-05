<p align="center"><span style="font-size:50px">ZTE2019 - 2019年中兴捧月算法精英挑战赛总决赛代码 </span>
</p>

## 赛题
- 迪杰斯特拉派
- 网络流量均衡赛题 
- 参赛人数：16
## 基本思路
- 应用多车道->图论重边建模
- 实现单个调度员部署与卸载函数（为了随机回溯）
- 以迪杰斯特拉算法为基础进行调度员规则应用
- 车道权重 1/负载 + 极小随机数（为了分离各车道）
- 同源同宿业务统一打包
- 发现部署阻塞进行自动拆包与重新打包
- 调度员增加时随机回溯
## 算法结果
- 运行时间：10个用例合计10s  
- 运行结果：10个用例平均1500  
- 排名：1/16  
## 声明
- 应提交要求所有类和方法整合在了单类中
